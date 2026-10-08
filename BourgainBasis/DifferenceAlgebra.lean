module
public import BourgainBasis.Contracts

@[expose] public section

noncomputable section
namespace BourgainBasis

def translate {m : ℕ} (h : Lattice m) (f : Lattice m → ℂ) : Lattice m → ℂ :=
  fun n => f (n+h)

theorem delta_translate {m : ℕ} (i : Fin m) (h : Lattice m) (f : Lattice m → ℂ) :
    delta i (translate h f) = translate h (delta i f) := by
  funext n
  simp only [delta, translate]
  congr 1
  congr 1
  abel

theorem delta_commute {m : ℕ} (i j : Fin m) (f : Lattice m → ℂ) :
    delta i (delta j f) = delta j (delta i f) := by
  funext n
  simp only [delta]
  rw [show n + Pi.single i 1 + Pi.single j 1 =
    n + Pi.single j 1 + Pi.single i 1 by abel]
  ring

theorem delta_product {m : ℕ} (i : Fin m) (f g : Lattice m → ℂ) (n : Lattice m) :
    delta i (fun n => f n*g n) n =
      delta i f n * g (n+Pi.single i 1) + f n * delta i g n := by
  simp only [delta]
  ring

theorem delta_star {m : ℕ} (i : Fin m) (f : Lattice m → ℂ) :
    delta i (fun n => star (f n)) = fun n => star (delta i f n) := by
  funext n
  simp [delta]

/-- The three terms needed for second differences; no differentiability assumed. -/
theorem delta_twice_product {m : ℕ} (i : Fin m) (f g : Lattice m → ℂ)
    (n : Lattice m) :
    delta i (delta i (fun n => f n*g n)) n =
      delta i (delta i f) n * g (n+Pi.single i 1+Pi.single i 1) +
      2 * delta i f n * delta i g (n+Pi.single i 1) + f n * delta i (delta i g) n := by
  simp only [delta]
  ring

end BourgainBasis
