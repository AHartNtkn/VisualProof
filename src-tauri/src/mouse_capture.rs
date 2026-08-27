#[cfg(target_os = "linux")]
use std::sync::{Mutex, OnceLock};

#[cfg(target_os = "linux")]
use raw_window_handle::{HasWindowHandle, RawWindowHandle};

#[cfg(target_os = "linux")]
use x11::xlib;

#[cfg(target_os = "linux")]
struct PointerGrab {
    display: *mut xlib::Display,
}

#[cfg(target_os = "linux")]
// Xlib access is serialized by POINTER_GRAB and this pointer is never used outside it.
unsafe impl Send for PointerGrab {}

#[cfg(target_os = "linux")]
static POINTER_GRAB: OnceLock<Mutex<Option<PointerGrab>>> = OnceLock::new();

pub fn set_game_mouse_capture(
    window: &tauri::WebviewWindow,
    captured: bool,
) -> Result<(), String> {
    #[cfg(target_os = "linux")]
    {
        return set_x11_pointer_capture(window, captured);
    }
    #[cfg(not(target_os = "linux"))]
    window
        .set_cursor_grab(captured)
        .map_err(|error| error.to_string())
}

#[cfg(target_os = "linux")]
fn set_x11_pointer_capture(window: &tauri::WebviewWindow, captured: bool) -> Result<(), String> {
    let grabs = POINTER_GRAB.get_or_init(|| Mutex::new(None));
    let mut current = grabs
        .lock()
        .map_err(|_| "native X11 pointer capture state is unavailable".to_owned())?;
    if captured {
        if current.is_some() {
            return Ok(());
        }
        let x11_window = match window
            .window_handle()
            .map_err(|error| error.to_string())?
            .as_raw()
        {
            RawWindowHandle::Xlib(handle) => handle.window,
            _ => return Err("Orchard requires an X11 game window for mouse capture".to_owned()),
        };
        let display = unsafe { xlib::XOpenDisplay(std::ptr::null()) };
        if display.is_null() {
            return Err("could not open the X11 display for mouse capture".to_owned());
        }
        let status = unsafe {
            xlib::XGrabPointer(
                display,
                x11_window,
                xlib::False,
                (xlib::PointerMotionMask | xlib::ButtonPressMask | xlib::ButtonReleaseMask) as u32,
                xlib::GrabModeAsync,
                xlib::GrabModeAsync,
                x11_window,
                0,
                xlib::CurrentTime,
            )
        };
        if status != xlib::GrabSuccess {
            unsafe { xlib::XCloseDisplay(display) };
            return Err(format!("X11 pointer capture was denied (status {status})"));
        }
        unsafe { xlib::XFlush(display) };
        *current = Some(PointerGrab { display });
        return Ok(());
    }
    if let Some(grab) = current.take() {
        unsafe {
            xlib::XUngrabPointer(grab.display, xlib::CurrentTime);
            xlib::XFlush(grab.display);
            xlib::XCloseDisplay(grab.display);
        }
    }
    Ok(())
}
