/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import MathUE.PMFProduct.Basic
import MathUE.PMFProduct.Bind
import MathUE.PMFProduct.Conditioning
import MathUE.PMFProduct.Update
import MathUE.PMFProduct.Independence
import MathUE.PMFProduct.Reindex

/-!
# Independent Product Distributions

Umbrella module. Split across `PMFProduct/`:

- `Basic` — `pmfPi` product distributions and the `Ignores` coordinate algebra.
- `Bind` — bind/factorization and pushforward lemmas.
- `Conditioning` — conditioning and disintegration.
- `Update` — coordinate-update lemmas and coordinate conditioning.
- `Independence` — bind/scalar coordinate independence.
- `Reindex` — pushforward of products through coordinate equivalences.
-/
