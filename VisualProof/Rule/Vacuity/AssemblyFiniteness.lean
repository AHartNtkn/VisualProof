import VisualProof.Data.Enumeration
import VisualProof.Rule.Vacuity.Assembly

namespace VisualProof.Rule.WholeAssemblyVacuity

open Diagram
open Theory

def WireExtension.freshEnumeration :
    (extension : WireExtension source target) →
      Enumeration extension.Fresh
  | .nil => {
      values := []
      complete := by intro fresh; nomatch fresh
    }
  | .retain extension => {
      values := extension.freshEnumeration.values.map .retainTail
      complete := by
        intro fresh
        cases fresh with
        | retainTail nested =>
            exact List.mem_map.mpr
              ⟨nested, extension.freshEnumeration.complete nested, rfl⟩
    }
  | .insert extension => {
      values := .inserted extension ::
        extension.freshEnumeration.values.map .insertTail
      complete := by
        intro fresh
        cases fresh with
        | inserted => simp
        | insertTail nested =>
            exact List.mem_cons_of_mem _ (List.mem_map.mpr
              ⟨nested, extension.freshEnumeration.complete nested, rfl⟩)
    }

mutual
  def IdentityOnlyExtension.freshWireEnumeration :
      (extension : IdentityOnlyExtension ambient source target) →
        Enumeration extension.FreshWire
    | .region locals items => {
        values := locals.freshEnumeration.values.map .local ++
          items.freshWireEnumeration.values.map .nested
        complete := fun wire => match wire with
          | .local fresh =>
              List.mem_append_left _ (List.mem_map.mpr
                ⟨fresh, locals.freshEnumeration.complete fresh, rfl⟩)
          | .nested fresh =>
              List.mem_append_right _ (List.mem_map.mpr
                ⟨fresh, items.freshWireEnumeration.complete fresh, rfl⟩)
      }

  def IdentityOnlyItemsExtension.freshWireEnumeration :
      (extension : IdentityOnlyItemsExtension ambient source target) →
        Enumeration extension.FreshWire
    | .nil => {
        values := []
        complete := by intro wire; nomatch wire
      }
    | .atom _ _ tail => {
        values := tail.freshWireEnumeration.values.map .atomTail
        complete := by
          intro wire
          cases wire with
          | atomTail nested =>
              exact List.mem_map.mpr
                ⟨nested, tail.freshWireEnumeration.complete nested, rfl⟩
      }
    | .identity _ tail => {
        values := tail.freshWireEnumeration.values.map .identityTail
        complete := by
          intro wire
          cases wire with
          | identityTail nested =>
              exact List.mem_map.mpr
                ⟨nested, tail.freshWireEnumeration.complete nested, rfl⟩
      }
    | .cut body tail => {
        values := body.freshWireEnumeration.values.map .cutHead ++
          tail.freshWireEnumeration.values.map .cutTail
        complete := by
          intro wire
          cases wire with
          | cutHead nested =>
              exact List.mem_append_left _ (List.mem_map.mpr
                ⟨nested, body.freshWireEnumeration.complete nested, rfl⟩)
          | cutTail nested =>
              exact List.mem_append_right _ (List.mem_map.mpr
                ⟨nested, tail.freshWireEnumeration.complete nested, rfl⟩)
      }
    | .addIdentity tail => {
        values := tail.freshWireEnumeration.values.map .addedIdentityTail
        complete := by
          intro wire
          cases wire with
          | addedIdentityTail nested =>
              exact List.mem_map.mpr
                ⟨nested, tail.freshWireEnumeration.complete nested, rfl⟩
      }
end

mutual
  def IdentityOnlyExtension.addedIdentityEnumeration :
      (extension : IdentityOnlyExtension ambient source target) →
        Enumeration extension.AddedIdentity
    | .region _ items => {
        values := items.addedIdentityEnumeration.values.map .item
        complete := by
          intro node
          cases node with
          | item nested =>
              exact List.mem_map.mpr
                ⟨nested, items.addedIdentityEnumeration.complete nested, rfl⟩
      }

  def IdentityOnlyItemsExtension.addedIdentityEnumeration :
      (extension : IdentityOnlyItemsExtension ambient source target) →
        Enumeration extension.AddedIdentity
    | .nil => {
        values := []
        complete := by intro node; nomatch node
      }
    | .atom _ _ tail => {
        values := tail.addedIdentityEnumeration.values.map .atomTail
        complete := by
          intro node
          cases node with
          | atomTail nested =>
              exact List.mem_map.mpr
                ⟨nested, tail.addedIdentityEnumeration.complete nested, rfl⟩
      }
    | .identity _ tail => {
        values := tail.addedIdentityEnumeration.values.map .identityTail
        complete := by
          intro node
          cases node with
          | identityTail nested =>
              exact List.mem_map.mpr
                ⟨nested, tail.addedIdentityEnumeration.complete nested, rfl⟩
      }
    | .cut body tail => {
        values := body.addedIdentityEnumeration.values.map .cutHead ++
          tail.addedIdentityEnumeration.values.map .cutTail
        complete := by
          intro node
          cases node with
          | cutHead nested =>
              exact List.mem_append_left _ (List.mem_map.mpr
                ⟨nested, body.addedIdentityEnumeration.complete nested, rfl⟩)
          | cutTail nested =>
              exact List.mem_append_right _ (List.mem_map.mpr
                ⟨nested, tail.addedIdentityEnumeration.complete nested, rfl⟩)
      }
    | .addIdentity tail => {
        values := .here ::
          tail.addedIdentityEnumeration.values.map .addedIdentityTail
        complete := by
          intro node
          cases node with
          | here => simp
          | addedIdentityTail nested =>
              exact List.mem_cons_of_mem _ (List.mem_map.mpr
                ⟨nested, tail.addedIdentityEnumeration.complete nested, rfl⟩)
      }
end

end VisualProof.Rule.WholeAssemblyVacuity
