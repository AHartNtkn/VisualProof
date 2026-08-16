import VisualProof.Diagram.Algebra

namespace VisualProof.Diagram

/-- One exact recursive region site, including the root site. -/
inductive Region.Site : {outer : List Theory.Sig} → Region outer → Type
  | root (region : Region outer) : Site region
  | cut (locals : List Theory.Sig)
      (before after : ItemSeq (outer ++ locals))
      (body : Region (outer ++ locals)) (child : body.Site) :
      Site (.mk locals (before.append (.cons (.cut body) after)))

/-- The corresponding site while traversing only an item sequence. -/
inductive ItemSeq.RegionSite : ItemSeq wires → Type
  | here (items : ItemSeq wires) : RegionSite items
  | cut (before after : ItemSeq wires) (body : Region wires)
      (child : body.Site) :
      RegionSite (before.append (.cons (.cut body) after))

def ItemSeq.RegionSite.prepend
    (head : Item wires) {tail : ItemSeq wires}
    (site : tail.RegionSite) : (ItemSeq.cons head tail).RegionSite :=
  match site with
  | .here _ => .here _
  | .cut before after body child =>
      .cut (.cons head before) after body child

def ItemSeq.RegionSite.toRegionSite
    (locals : List Theory.Sig) {items : ItemSeq (outer ++ locals)}
    (site : items.RegionSite) : (Region.mk locals items).Site :=
  match site with
  | .here _ => .root _
  | .cut before after body child => .cut locals before after body child

def Region.Site.outer {outer : List Theory.Sig} {region : Region outer} :
    region.Site → List Theory.Sig
  | .root _ => outer
  | .cut _ _ _ _ child => child.outer

def Region.Site.body {outer : List Theory.Sig} {region : Region outer} :
    (site : Region.Site region) → Region site.outer
  | .root region => region
  | .cut _ _ _ _ child => child.body

def Region.Site.context {outer : List Theory.Sig} {region : Region outer} :
    (site : Region.Site region) →
    DiagramContext outer site.outer
  | .root _ => .hole
  | .cut locals before after _ child =>
      .cut locals before after child.context

@[simp] theorem Region.Site.fill_context (site : Region.Site region) :
    site.context.fill site.body = region := by
  induction site with
  | root => rfl
  | cut locals before after body child induction =>
      simp only [Region.Site.context, DiagramContext.fill, Region.Site.body]
      exact congrArg (Region.mk locals)
        (congrArg (fun selected => before.append (.cons selected after))
          (congrArg Item.cut induction))

end VisualProof.Diagram
