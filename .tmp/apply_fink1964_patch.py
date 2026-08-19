from pathlib import Path

path = Path("Literature/Fink1964.lean")
text = path.read_text(encoding="utf-8")

old = '''  · apply Continuous.mul
    · apply Continuous.mul
      · fun_prop
      · apply continuous_finsetProd (Finset.univ.erase who)
        intro i hi
        fun_prop
'''
new = '''  · apply Continuous.mul
    · apply Continuous.mul
      · exact (continuous_apply (a who)).comp
          (continuous_subtype_val.comp
            ((continuous_apply (s, who)).comp
              (continuous_fst.comp continuous_snd)))
      · apply continuous_finsetProd (Finset.univ.erase who)
        intro i hi
        exact (continuous_apply (a i)).comp
          (continuous_subtype_val.comp
            ((continuous_apply (s, i)).comp continuous_fst))
'''
if old not in text:
    raise RuntimeError("property_a coordinate block not found")
text = text.replace(old, new, 1)

# Give the closed-fiber proof enough room to unfold the dependent simplex product.
old = '''/-- Closedness of each fiber `φ(x)`. -/
theorem phi_isClosed
'''
new = '''/-- Closedness of each fiber `φ(x)`. -/
set_option maxHeartbeats 800000 in
theorem phi_isClosed
'''
if old not in text:
    raise RuntimeError("phi_isClosed header not found")
text = text.replace(old, new, 1)

path.write_text(text, encoding="utf-8")
