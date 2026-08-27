#[cfg(target_os = "linux")]
use std::sync::{Mutex, OnceLock};

#[cfg(target_os = "linux")]
use raw_window_handle::{HasDisplayHandle, HasWindowHandle, RawDisplayHandle, RawWindowHandle};

#[cfg(target_os = "linux")]
use x11::{xfixes, xlib};

#[cfg(target_os = "linux")]
struct PointerConfinement {
    display: *mut xlib::Display,
    barriers: [xfixes::PointerBarrier; 4],
    left: i32,
    top: i32,
    right: i32,
    bottom: i32,
}

#[cfg(target_os = "linux")]
// Xlib access is serialized by POINTER_CONFINEMENT and this pointer is never used outside it.
unsafe impl Send for PointerConfinement {}

#[cfg(target_os = "linux")]
static POINTER_CONFINEMENT: OnceLock<Mutex<Option<PointerConfinement>>> = OnceLock::new();

pub fn set_game_mouse_capture(window: &tauri::WebviewWindow, captured: bool) -> Result<(), String> {
    #[cfg(target_os = "linux")]
    {
        set_x11_pointer_capture(window, captured)
    }
    #[cfg(not(target_os = "linux"))]
    window
        .set_cursor_grab(captured)
        .map_err(|error| error.to_string())
}

#[cfg(target_os = "linux")]
fn set_x11_pointer_capture(window: &tauri::WebviewWindow, captured: bool) -> Result<(), String> {
    let confinements = POINTER_CONFINEMENT.get_or_init(|| Mutex::new(None));
    let mut current = confinements
        .lock()
        .map_err(|_| "native X11 pointer capture state is unavailable".to_owned())?;
    if captured {
        replace_confinement(&mut current, window)?;
    } else {
        destroy_confinement(current.take());
    }
    Ok(())
}

#[cfg(target_os = "linux")]
fn create_confinement(
    window: &(impl HasWindowHandle + HasDisplayHandle),
) -> Result<PointerConfinement, String> {
    let x11_window = match window
        .window_handle()
        .map_err(|error| error.to_string())?
        .as_raw()
    {
        RawWindowHandle::Xlib(handle) => handle.window,
        _ => return Err("Orchard requires an X11 game window for mouse capture".to_owned()),
    };
    let display = match window
        .display_handle()
        .map_err(|error| error.to_string())?
        .as_raw()
    {
        RawDisplayHandle::Xlib(handle) => handle
            .display
            .ok_or_else(|| "Orchard's X11 display handle is missing".to_owned())?
            .as_ptr()
            .cast::<xlib::Display>(),
        _ => return Err("Orchard requires an X11 display for mouse capture".to_owned()),
    };
    let mut event_base = 0;
    let mut error_base = 0;
    if unsafe { xfixes::XFixesQueryExtension(display, &mut event_base, &mut error_base) }
        == xlib::False
    {
        return Err("XFixes pointer barriers are unavailable".to_owned());
    }

    let mut attributes: xlib::XWindowAttributes = unsafe { std::mem::zeroed() };
    if unsafe { xlib::XGetWindowAttributes(display, x11_window, &mut attributes) } == 0 {
        return Err("could not read the Orchard window bounds".to_owned());
    }
    let root = unsafe { xlib::XDefaultRootWindow(display) };
    let mut left = 0;
    let mut top = 0;
    let mut child = 0;
    if unsafe {
        xlib::XTranslateCoordinates(
            display, x11_window, root, 0, 0, &mut left, &mut top, &mut child,
        )
    } == 0
    {
        return Err("could not locate the Orchard window on the X11 display".to_owned());
    }
    let right = left + attributes.width;
    let bottom = top + attributes.height;
    let barrier = |x1, y1, x2, y2, directions| unsafe {
        xfixes::XFixesCreatePointerBarrier(
            display,
            root,
            x1,
            y1,
            x2,
            y2,
            directions,
            0,
            std::ptr::null_mut(),
        )
    };
    let barriers = [
        barrier(left, top, left, bottom, 0),
        barrier(right, top, right, bottom, 0),
        barrier(left, top, right, top, 0),
        barrier(left, bottom, right, bottom, 0),
    ];
    if barriers.contains(&0) {
        for created in barriers.into_iter().filter(|barrier| *barrier != 0) {
            unsafe { xfixes::XFixesDestroyPointerBarrier(display, created) };
        }
        return Err("could not create X11 pointer barriers".to_owned());
    }
    unsafe { xlib::XFlush(display) };
    Ok(PointerConfinement {
        display,
        barriers,
        left,
        top,
        right,
        bottom,
    })
}

#[cfg(target_os = "linux")]
fn replace_confinement(
    current: &mut Option<PointerConfinement>,
    window: &(impl HasWindowHandle + HasDisplayHandle),
) -> Result<(), String> {
    let previous = current.take();
    let previous_bounds = previous
        .as_ref()
        .map(|value| (value.left, value.top, value.right, value.bottom));
    destroy_confinement(previous);
    let next = create_confinement(window)?;
    let mut pointer_root = 0;
    let mut pointer_child = 0;
    let mut pointer_x = 0;
    let mut pointer_y = 0;
    let mut pointer_window_x = 0;
    let mut pointer_window_y = 0;
    let mut pointer_mask = 0;
    let root = unsafe { xlib::XDefaultRootWindow(next.display) };
    if unsafe {
        xlib::XQueryPointer(
            next.display,
            root,
            &mut pointer_root,
            &mut pointer_child,
            &mut pointer_x,
            &mut pointer_y,
            &mut pointer_window_x,
            &mut pointer_window_y,
            &mut pointer_mask,
        )
    } == xlib::False
    {
        destroy_confinement(Some(next));
        return Err("could not locate the X11 pointer".to_owned());
    }

    let target = previous_bounds.map_or_else(
        || {
            if pointer_x >= next.left
                && pointer_x < next.right
                && pointer_y >= next.top
                && pointer_y < next.bottom
            {
                (pointer_x, pointer_y)
            } else {
                ((next.left + next.right) / 2, (next.top + next.bottom) / 2)
            }
        },
        |(previous_left, previous_top, previous_right, previous_bottom)| {
            if pointer_x >= previous_left
                && pointer_x < previous_right
                && pointer_y >= previous_top
                && pointer_y < previous_bottom
            {
                (
                    (pointer_x + next.left - previous_left).clamp(next.left, next.right - 1),
                    (pointer_y + next.top - previous_top).clamp(next.top, next.bottom - 1),
                )
            } else {
                ((next.left + next.right) / 2, (next.top + next.bottom) / 2)
            }
        },
    );
    if target != (pointer_x, pointer_y) {
        unsafe {
            xlib::XWarpPointer(next.display, 0, root, 0, 0, 0, 0, target.0, target.1);
            xlib::XFlush(next.display);
        }
    }
    *current = Some(next);
    Ok(())
}

#[cfg(target_os = "linux")]
fn destroy_confinement(confinement: Option<PointerConfinement>) {
    if let Some(confinement) = confinement {
        unsafe {
            for barrier in confinement.barriers {
                xfixes::XFixesDestroyPointerBarrier(confinement.display, barrier);
            }
            xlib::XFlush(confinement.display);
        }
    }
}
