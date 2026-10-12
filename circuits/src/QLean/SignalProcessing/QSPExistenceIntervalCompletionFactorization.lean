import QLean.SignalProcessing.QSPExistenceInverseReciprocalRootClosure

namespace SpectralSamplingProof.Analytic

open VerifiedCircuitCore

noncomputable section

/-!  The three commuting involutions used below are kept explicit.  The
    multiset argument is written at the level of counts; no squarefree or
    membership-only root argument is used. -/

def starNegMap020 (z : ℂ) : ℂ := -(starRingEnd ℂ) z

@[simp] lemma starNegMap020_apply (z : ℂ) :
    starNegMap020 z = -(starRingEnd ℂ) z := rfl

lemma starNegMap020_involutive : Function.Involutive starNegMap020 := by
  intro z
  simp [starNegMap020]

lemma starNegMap020_injective : Function.Injective starNegMap020 :=
  starNegMap020_involutive.injective

lemma invStar127_involutive_fun : Function.Involutive invStar127 := by
  intro z
  exact invStar127_involutive z

lemma starNegMap020_invStar_comm (z : ℂ) :
    starNegMap020 (invStar127 z) = invStar127 (starNegMap020 z) := by
  simp [starNegMap020, invStar127]

lemma starNegMap020_star_comm (z : ℂ) :
    starNegMap020 ((starRingEnd ℂ) z) = (starRingEnd ℂ) (starNegMap020 z) := by
  simp [starNegMap020]

lemma invStar127_injective : Function.Injective invStar127 :=
  invStar127_involutive_fun.injective

lemma multiset_map_starNeg020_eq_self
    (s : Multiset ℂ)
    (hstar : Multiset.map (starRingEnd ℂ) s = s)
    (hneg : Multiset.map (fun z : ℂ => -z) s = s) :
    Multiset.map starNegMap020 s = s := by
  calc
    Multiset.map starNegMap020 s =
        Multiset.map (fun z : ℂ => -z)
          (Multiset.map (starRingEnd ℂ) s) := by
            rw [Multiset.map_map]
            rfl
    _ = Multiset.map (fun z : ℂ => -z) s := by rw [hstar]
    _ = s := hneg

def orbitFin020 (a : ℂ) : Finset ℂ :=
  {a, starNegMap020 a, invStar127 a,
    starNegMap020 (invStar127 a)}

def starNegEmb020 : ℂ ↪ ℂ :=
  ⟨starNegMap020, starNegMap020_injective⟩

def invStarEmb020 : ℂ ↪ ℂ :=
  ⟨invStar127, invStar127_injective⟩

lemma orbitFin020_map_j_finset (a : ℂ) :
    Finset.map starNegEmb020 (orbitFin020 a) = orbitFin020 a := by
  ext z
  simp [orbitFin020, starNegEmb020, starNegMap020, invStar127]
  tauto

lemma orbitFin020_map_i_finset (a : ℂ) :
    Finset.map invStarEmb020 (orbitFin020 a) = orbitFin020 a := by
  ext z
  simp [orbitFin020, invStarEmb020, starNegMap020, invStar127]
  tauto

lemma orbitFin020_mem_of_mem
    (t : Multiset ℂ) (a : ℂ) (ha : a ∈ t)
    (hj : Multiset.map starNegMap020 t = t)
    (hi : Multiset.map invStar127 t = t)
    {z : ℂ} (hz : z ∈ orbitFin020 a) : z ∈ t := by
  simp only [orbitFin020, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact ha
  · have hm := Multiset.mem_map_of_mem starNegMap020 ha
    rw [hj] at hm
    simpa [starNegMap020] using hm
  · have hm := Multiset.mem_map_of_mem invStar127 ha
    rw [hi] at hm
    exact hm
  · have hm := Multiset.mem_map_of_mem invStar127 ha
    rw [hi] at hm
    have hm' := Multiset.mem_map_of_mem starNegMap020 hm
    rw [hj] at hm'
    exact hm'

lemma finset_val_le_of_mem020
    (t : Multiset ℂ) (K : Finset ℂ)
    (hmem : ∀ z ∈ K, z ∈ t) :
    (K.1 : Multiset ℂ) ≤ t := by
  rw [Multiset.le_iff_count]
  intro z
  by_cases hz : z ∈ K
  · have hcount_le : (K.1 : Multiset ℂ).count z ≤ 1 :=
      (Multiset.nodup_iff_count_le_one.mp K.nodup) z
    have hcount_pos : 0 < (K.1 : Multiset ℂ).count z :=
      Multiset.count_pos.mpr (by simpa using hz)
    have htpos : 0 < t.count z := Multiset.count_pos.mpr (hmem z hz)
    omega
  · simp [hz]

lemma orbitFin020_map_starNeg
    (a : ℂ) :
    (orbitFin020 a).1.map starNegMap020 =
      (orbitFin020 a).1 := by
  have h := congrArg (fun K : Finset ℂ => K.1)
    (orbitFin020_map_j_finset a)
  simpa [Finset.map_val, starNegEmb020] using h

lemma orbitFin020_map_invStar
    (a : ℂ) :
    (orbitFin020 a).1.map invStar127 =
      (orbitFin020 a).1 := by
  have h := congrArg (fun K : Finset ℂ => K.1)
    (orbitFin020_map_i_finset a)
  simpa [Finset.map_val, invStarEmb020] using h

lemma orbitFin020_map_star
    (a : ℂ) :
    Multiset.map (starRingEnd ℂ)
        ((orbitFin020 a).1 +
          Multiset.map (starRingEnd ℂ) (orbitFin020 a).1) =
      (orbitFin020 a).1 +
        Multiset.map (starRingEnd ℂ) (orbitFin020 a).1 := by
  rw [Multiset.map_add, Multiset.map_map]
  simp only [Function.comp_def]
  have hstarstar :
      Multiset.map (fun z : ℂ => (starRingEnd ℂ) ((starRingEnd ℂ) z))
          (orbitFin020 a).1 = (orbitFin020 a).1 := by
    calc
      Multiset.map
          (fun z : ℂ => (starRingEnd ℂ) ((starRingEnd ℂ) z))
          (orbitFin020 a).1 =
          Multiset.map (fun z : ℂ => z) (orbitFin020 a).1 := by
            refine Multiset.map_congr rfl ?_
            intro z hz
            exact star_involutive127 z
      _ = (orbitFin020 a).1 := by simp
  rw [hstarstar]
  ac_rfl

lemma orbitFin020_map_starNeg_total
    (a : ℂ) :
    Multiset.map starNegMap020
        ((orbitFin020 a).1 +
          Multiset.map (starRingEnd ℂ) (orbitFin020 a).1) =
      (orbitFin020 a).1 +
        Multiset.map (starRingEnd ℂ) (orbitFin020 a).1 := by
  rw [Multiset.map_add, orbitFin020_map_starNeg]
  rw [Multiset.map_map]
  rw [show (starNegMap020 ∘ starRingEnd ℂ) =
      (starRingEnd ℂ) ∘ starNegMap020 by
        funext z
        exact starNegMap020_star_comm z]
  rw [← Multiset.map_map, orbitFin020_map_starNeg]

lemma orbitFin020_map_invStar_total
    (a : ℂ) :
    Multiset.map invStar127
        ((orbitFin020 a).1 +
          Multiset.map (starRingEnd ℂ) (orbitFin020 a).1) =
      (orbitFin020 a).1 +
        Multiset.map (starRingEnd ℂ) (orbitFin020 a).1 := by
  rw [Multiset.map_add, orbitFin020_map_invStar]
  rw [Multiset.map_map]
  rw [show (invStar127 ∘ starRingEnd ℂ) =
      (starRingEnd ℂ) ∘ invStar127 by
        funext z
        simp [invStar127]]
  rw [← Multiset.map_map, orbitFin020_map_invStar]

lemma star_eq_self_of_star_mem_orbit020
    (a : ℂ) (h : (starRingEnd ℂ) a ∈ orbitFin020 a) :
    (starRingEnd ℂ) a = a := by
  simp only [orbitFin020, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h
  · exact h
  · have hs := congrArg (starRingEnd ℂ) h
    have ha : a = 0 := by
      apply (neg_eq_self.mp ?_)
      simpa [starNegMap020] using hs.symm
    simp [ha]
  · have ha : a = a⁻¹ := by
      apply (starRingEnd ℂ).injective
      simpa [invStar127] using h
    by_cases ha0 : a = 0
    · simp [ha0]
    have haa : a * a = 1 := by
      calc
        a * a = a * a⁻¹ := congrArg (fun x : ℂ => a * x) ha
        _ = 1 := mul_inv_cancel₀ ha0
    rcases (mul_self_eq_one_iff.mp haa) with ha1 | ha1
    · simp [ha1]
    · simp [ha1]
  · have hfour : (starRingEnd ℂ) a = -a⁻¹ := by
      simpa [starNegMap020, invStar127] using h
    by_cases ha0 : a = 0
    · simp [ha0]
    have hnorm : (Complex.normSq a : ℂ) = -1 := by
      calc
        (Complex.normSq a : ℂ) = a * (starRingEnd ℂ) a := by
          symm
          exact Complex.mul_conj a
        _ = a * (-a⁻¹) := by rw [hfour]
        _ = -(a * a⁻¹) := by ring
        _ = -1 := by
          rw [mul_inv_cancel₀ ha0]
    have hnormR : (Complex.normSq a : ℝ) = -1 := by
      exact_mod_cast hnorm
    have hn : 0 ≤ Complex.normSq a := Complex.normSq_nonneg a
    linarith

def starEmb020 : ℂ ↪ ℂ :=
  ⟨starRingEnd ℂ, star_involutive127.injective⟩

def orbitStarFin020 (a : ℂ) : Finset ℂ :=
  Finset.map starEmb020 (orbitFin020 a)

lemma orbitStarFin020_val (a : ℂ) :
    (orbitStarFin020 a).1 =
      Multiset.map (starRingEnd ℂ) (orbitFin020 a).1 := by
  simp [orbitStarFin020, starEmb020]

lemma orbitStarFin020_mem_of_mem
    (t : Multiset ℂ) (a : ℂ) (ha : a ∈ t)
    (hstar : Multiset.map (starRingEnd ℂ) t = t)
    (hj : Multiset.map starNegMap020 t = t)
    (hi : Multiset.map invStar127 t = t)
    {z : ℂ} (hz : z ∈ orbitStarFin020 a) : z ∈ t := by
  rw [orbitStarFin020, Finset.mem_map] at hz
  rcases hz with ⟨y, hy, rfl⟩
  have hmy := orbitFin020_mem_of_mem t a ha hj hi hy
  have hm := Multiset.mem_map_of_mem (starRingEnd ℂ) hmy
  rw [hstar] at hm
  simpa [starEmb020] using hm

lemma orbitFin020_map_star_finset (a : ℂ) :
    Finset.map starEmb020 (orbitFin020 a) =
      orbitFin020 ((starRingEnd ℂ) a) := by
  ext z
  simp [orbitFin020, starEmb020, starNegMap020, invStar127]

lemma orbitFin020_eq_of_mem (a b : ℂ)
    (hb : b ∈ orbitFin020 a) :
    orbitFin020 b = orbitFin020 a := by
  simp only [orbitFin020, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · rfl
  · rw [show orbitFin020 (starNegMap020 a) =
      orbitFin020 a by
        ext z
        simp [orbitFin020, starNegMap020, invStar127]
        tauto]
  · rw [show orbitFin020 (invStar127 a) =
      orbitFin020 a by
        ext z
        simp [orbitFin020, starNegMap020, invStar127]
        tauto]
  · rw [show orbitFin020 (starNegMap020 (invStar127 a)) =
      orbitFin020 a by
        ext z
        simp [orbitFin020, starNegMap020, invStar127]
        tauto]

lemma orbitStarFin020_eq_orbit_of_overlap020 (a : ℂ)
    (h : (starRingEnd ℂ) a ∈ orbitFin020 a) :
    orbitStarFin020 a = orbitFin020 a := by
  rw [orbitStarFin020, orbitFin020_map_star_finset]
  exact orbitFin020_eq_of_mem a ((starRingEnd ℂ) a) h

lemma finset_add_val_le_of_mem_disjoint020
    (t : Multiset ℂ) (K L : Finset ℂ)
    (hK : ∀ z ∈ K, z ∈ t)
    (hL : ∀ z ∈ L, z ∈ t)
    (hdisj : Disjoint K L) :
    (K.1 : Multiset ℂ) + L.1 ≤ t := by
  rw [Multiset.le_iff_count]
  intro z
  by_cases hzK : z ∈ K
  · have hzL : z ∉ L := (Finset.disjoint_left.mp hdisj) hzK
    have hKle : (K.1 : Multiset ℂ).count z ≤ 1 :=
      (Multiset.nodup_iff_count_le_one.mp K.nodup) z
    have hKpos : 0 < (K.1 : Multiset ℂ).count z :=
      Multiset.count_pos.mpr (by simpa using hzK)
    have htpos : 0 < t.count z :=
      Multiset.count_pos.mpr (hK z hzK)
    have hLzero : (L.1 : Multiset ℂ).count z = 0 := by
      simp [hzL]
    simp only [Multiset.count_add, hLzero, add_zero]
    omega
  · by_cases hzL : z ∈ L
    · have hLle : (L.1 : Multiset ℂ).count z ≤ 1 :=
        (Multiset.nodup_iff_count_le_one.mp L.nodup) z
      have hLpos : 0 < (L.1 : Multiset ℂ).count z :=
        Multiset.count_pos.mpr (by simpa using hzL)
      have htpos : 0 < t.count z :=
        Multiset.count_pos.mpr (hL z hzL)
      have hKzero : (K.1 : Multiset ℂ).count z = 0 := by
        simp [hzK]
      simp only [Multiset.count_add, hKzero, zero_add]
      omega
    · have hKzero : (K.1 : Multiset ℂ).count z = 0 := by
        simp [hzK]
      have hLzero : (L.1 : Multiset ℂ).count z = 0 := by
        simp [hzL]
      simp [Multiset.count_add, hKzero, hLzero]

lemma residual_decomposition020
    (t c : Multiset ℂ) (hle : c ≤ t) :
    t = c + (t - c) := by
  calc
    t = t - c + c := (Multiset.sub_add_cancel hle).symm
    _ = c + (t - c) := by ac_rfl

lemma residual_invariant020
    (t c : Multiset ℂ) (hle : c ≤ t)
    (f : ℂ → ℂ)
    (ht : Multiset.map f t = t)
    (hc : Multiset.map f c = c) :
    Multiset.map f (t - c) = t - c := by
  have hdec := residual_decomposition020 t c hle
  have hm := congrArg (Multiset.map f) hdec
  rw [Multiset.map_add, ht, hc] at hm
  have hcancel : c + Multiset.map f (t - c) = c + (t - c) :=
    hm.symm.trans hdec
  exact add_left_cancel hcancel

lemma residual_lt020
    (t c : Multiset ℂ) (hle : c ≤ t) (hc : c ≠ 0) :
    t - c < t := by
  rw [Multiset.lt_iff_cons_le]
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hc
  refine ⟨a, ?_⟩
  have hsingle : ({a} : Multiset ℂ) ≤ c :=
    Multiset.singleton_le.mpr ha
  have hplus := add_le_add_right hsingle (t - c)
  have hplus' : {a} + (t - c) ≤ c + (t - c) := by
    simpa [add_comm, add_left_comm, add_assoc] using hplus
  have hplus'' : a ::ₘ (t - c) ≤ c + (t - c) := by
    simpa using hplus'
  exact hplus''.trans_eq (residual_decomposition020 t c hle).symm

lemma star_mem_of_orbit_intersection020 (a : ℂ)
    (h : ∃ z, z ∈ orbitFin020 a ∧ z ∈ orbitStarFin020 a) :
    (starRingEnd ℂ) a ∈ orbitFin020 a := by
  have mem_j : ∀ {z : ℂ}, z ∈ orbitFin020 a →
      starNegMap020 z ∈ orbitFin020 a := by
    intro z hz
    have hz' : starNegMap020 z ∈
        Finset.map starNegEmb020 (orbitFin020 a) :=
      Finset.mem_map.mpr ⟨z, hz, rfl⟩
    rw [orbitFin020_map_j_finset a] at hz'
    exact hz'
  have mem_i : ∀ {z : ℂ}, z ∈ orbitFin020 a →
      invStar127 z ∈ orbitFin020 a := by
    intro z hz
    have hz' : invStar127 z ∈
        Finset.map invStarEmb020 (orbitFin020 a) :=
      Finset.mem_map.mpr ⟨z, hz, rfl⟩
    rw [orbitFin020_map_i_finset a] at hz'
    exact hz'
  rcases h with ⟨z, hzK, hzL⟩
  rw [orbitStarFin020, Finset.mem_map] at hzL
  rcases hzL with ⟨y, hy, hzy⟩
  simp only [orbitFin020, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · rw [← hzy] at hzK
    simpa [starEmb020] using hzK
  · have hJ := mem_j hzK
    rw [← hzy] at hJ
    simpa [starEmb020, starNegMap020] using hJ
  · have hI := mem_i hzK
    rw [← hzy] at hI
    simpa [starEmb020, invStar127] using hI
  · have hI := mem_i hzK
    have hJ := mem_j hI
    rw [← hzy] at hJ
    simpa [starEmb020, starNegMap020, invStar127] using hJ

lemma star_fixed_on_orbit_of_overlap020 (a : ℂ)
    (h : (starRingEnd ℂ) a ∈ orbitFin020 a) :
    ∀ z ∈ orbitFin020 a, (starRingEnd ℂ) z = z := by
  have ha := star_eq_self_of_star_mem_orbit020 a h
  intro z hz
  simp only [orbitFin020, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact ha
  · simp [starNegMap020, ha]
  · simp [invStar127, ha]
  · simp [starNegMap020, invStar127, ha]

lemma star_fixed_mem_orbitStar_implies_orbit020
    (a z : ℂ) (hzfix : (starRingEnd ℂ) z = z)
    (hz : z ∈ orbitStarFin020 a) : z ∈ orbitFin020 a := by
  rw [orbitStarFin020, Finset.mem_map] at hz
  rcases hz with ⟨y, hy, hzy⟩
  have h := congrArg (starRingEnd ℂ) hzy
  have hyz : y = (starRingEnd ℂ) z := by
    simpa [starEmb020] using h
  rw [hzfix] at hyz
  simpa [hyz] using hy

lemma star_fixed_not_mem_disjoint020 (a z : ℂ)
    (hdisj : Disjoint (orbitFin020 a) (orbitStarFin020 a))
    (hzfix : (starRingEnd ℂ) z = z) :
    z ∉ orbitFin020 a ∧ z ∉ orbitStarFin020 a := by
  constructor
  · intro hzK
    have hzs : (starRingEnd ℂ) z ∈ orbitStarFin020 a := by
      rw [orbitStarFin020, Finset.mem_map]
      exact ⟨z, hzK, rfl⟩
    have hzL : z ∈ orbitStarFin020 a := by simpa [hzfix] using hzs
    exact (Finset.disjoint_left.mp hdisj hzK) hzL
  · intro hzL
    have hzK := star_fixed_mem_orbitStar_implies_orbit020 a z hzfix hzL
    exact (Finset.disjoint_left.mp hdisj hzK) hzL

lemma even_double_finset_count020
    (K : Finset ℂ) (z : ℂ) :
    Even ((K.1 : Multiset ℂ).count z + K.1.count z) := by
  by_cases hz : z ∈ K
  · have hk : (K.1 : Multiset ℂ).count z = 1 := by
      have hk_le := (Multiset.nodup_iff_count_le_one.mp K.nodup) z
      have hk_pos := Multiset.count_pos.mpr (show z ∈ (K.1 : Multiset ℂ) by
        simpa using hz)
      omega
    simp [hk]
  · have hk : (K.1 : Multiset ℂ).count z = 0 := by simp [hz]
    simp [hk]

lemma even_residual_count020
    (s c u : Multiset ℂ) (hdec : s = c + u) (z : ℂ)
    (hs : Even (s.count z)) (hc : Even (c.count z)) :
    Even (u.count z) := by
  have hcount := congrArg (fun m : Multiset ℂ => m.count z) hdec
  simp only [Multiset.count_add] at hcount
  rcases hs with ⟨m, hm⟩
  rcases hc with ⟨n, hn⟩
  refine ⟨m - n, ?_⟩
  omega

lemma finset_double_val_le_of_even020
    (t : Multiset ℂ) (K : Finset ℂ)
    (hmem : ∀ z ∈ K, z ∈ t)
    (heven : ∀ z ∈ K, Even (t.count z)) :
    (K.1 : Multiset ℂ) + K.1 ≤ t := by
  rw [Multiset.le_iff_count]
  intro z
  by_cases hz : z ∈ K
  · have hkle : (K.1 : Multiset ℂ).count z ≤ 1 :=
      (Multiset.nodup_iff_count_le_one.mp K.nodup) z
    have hkpos : 0 < (K.1 : Multiset ℂ).count z :=
      Multiset.count_pos.mpr (by simpa using hz)
    have htpos : 0 < t.count z :=
      Multiset.count_pos.mpr (hmem z hz)
    rcases heven z hz with ⟨n, hn⟩
    have hkeq : (K.1 : Multiset ℂ).count z = 1 := by omega
    simp only [Multiset.count_add]
    omega
  · simp [hz]

theorem exists_star_neg_inv_half020
    (s : Multiset ℂ)
    (hstar : Multiset.map (starRingEnd ℂ) s = s)
    (hneg : Multiset.map (fun z : ℂ => -z) s = s)
    (hinv : Multiset.map invStar127 s = s)
    (hfixed : ∀ z : ℂ, (starRingEnd ℂ) z = z →
      Even (s.count z)) :
    ∃ q : Multiset ℂ,
      s = q + Multiset.map (starRingEnd ℂ) q ∧
      Multiset.map starNegMap020 q = q ∧
      Multiset.map invStar127 q = q := by
  have hP : ∀ n : ℕ,
      ∀ t : Multiset ℂ, t.card = n →
      (Multiset.map (starRingEnd ℂ) t = t) →
      (Multiset.map (fun z : ℂ => -z) t = t) →
      (Multiset.map invStar127 t = t) →
      (∀ z : ℂ, (starRingEnd ℂ) z = z → Even (t.count z)) →
      ∃ q : Multiset ℂ,
        t = q + Multiset.map (starRingEnd ℂ) q ∧
        Multiset.map starNegMap020 q = q ∧
        Multiset.map invStar127 q = q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t ht hst hng hiv hfix
      by_cases ht0 : t = 0
      · subst t
        refine ⟨0, by simp, by simp, by simp⟩
      · obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero ht0
        have hj : Multiset.map starNegMap020 t = t :=
          multiset_map_starNeg020_eq_self t hst hng
        have hi : Multiset.map invStar127 t = t := hiv
        let K : Finset ℂ := orbitFin020 a
        let L : Finset ℂ := orbitStarFin020 a
        have hKmem : ∀ z ∈ K, z ∈ t := by
          intro z hz
          simpa [K] using orbitFin020_mem_of_mem t a ha hj hi hz
        have hLmem : ∀ z ∈ L, z ∈ t := by
          intro z hz
          simpa [L] using orbitStarFin020_mem_of_mem t a ha hst hj hi hz
        have hKj : Multiset.map starNegMap020 K.1 = K.1 := by
          simpa [K] using orbitFin020_map_starNeg a
        have hKi : Multiset.map invStar127 K.1 = K.1 := by
          simpa [K] using orbitFin020_map_invStar a
        have hLval : L.1 = Multiset.map (starRingEnd ℂ) K.1 := by
          simpa [K, L] using orbitStarFin020_val a
        have haK : a ∈ K := by simp [K, orbitFin020]
        by_cases hdisj : Disjoint K L
        · have hKL : K.1 + L.1 ≤ t :=
            finset_add_val_le_of_mem_disjoint020 t K L hKmem hLmem hdisj
          have hKLne : K.1 + L.1 ≠ 0 := by
            intro hz
            have haz : a ∈ K.1 + L.1 := by
              simp [haK]
            rw [hz] at haz
            simp at haz
          let u : Multiset ℂ := t - (K.1 + L.1)
          have hdec : t = (K.1 + L.1) + u := by
            dsimp [u]
            exact residual_decomposition020 t (K.1 + L.1) hKL
          have hlt : u < t := by
            dsimp [u]
            exact residual_lt020 t (K.1 + L.1) hKL hKLne
          have hcard : u.card < n := by
            have hc : u.card < t.card := Multiset.card_lt_card hlt
            exact hc.trans_eq ht
          have hcstar : Multiset.map (starRingEnd ℂ) (K.1 + L.1) =
              K.1 + L.1 := by
            rw [hLval]
            exact orbitFin020_map_star a
          have hcj : Multiset.map starNegMap020 (K.1 + L.1) =
              K.1 + L.1 := by
            rw [hLval]
            exact orbitFin020_map_starNeg_total a
          have hci : Multiset.map invStar127 (K.1 + L.1) =
              K.1 + L.1 := by
            rw [hLval]
            exact orbitFin020_map_invStar_total a
          have hcneg : Multiset.map (fun z : ℂ => -z) (K.1 + L.1) =
              K.1 + L.1 := by
            rw [show (fun z : ℂ => -z) =
                starNegMap020 ∘ (starRingEnd ℂ) by
                  funext z
                  simp [starNegMap020]]
            rw [← Multiset.map_map, hcstar, hcj]
          have hcfixed : ∀ z : ℂ, (starRingEnd ℂ) z = z →
              Even ((K.1 + L.1).count z) := by
            intro z hz
            have hdisj' : Disjoint (orbitFin020 a) (orbitStarFin020 a) := by
              simpa [K, L] using hdisj
            have hnot := star_fixed_not_mem_disjoint020 a z hdisj' hz
            have hKzero : K.1.count z = 0 := by simp [K, hnot.1]
            have hLzero : L.1.count z = 0 := by simp [L, hnot.2]
            simp [Multiset.count_add, hKzero, hLzero]
          have hustar : Multiset.map (starRingEnd ℂ) u = u := by
            dsimp [u]
            exact residual_invariant020 t (K.1 + L.1) hKL
              (starRingEnd ℂ) hst hcstar
          have huj : Multiset.map starNegMap020 u = u := by
            dsimp [u]
            exact residual_invariant020 t (K.1 + L.1) hKL
              starNegMap020 hj hcj
          have hui : Multiset.map invStar127 u = u := by
            dsimp [u]
            exact residual_invariant020 t (K.1 + L.1) hKL
              invStar127 hiv hci
          have huneg : Multiset.map (fun z : ℂ => -z) u = u := by
            dsimp [u]
            exact residual_invariant020 t (K.1 + L.1) hKL
              (fun z : ℂ => -z) hng hcneg
          have hufix : ∀ z : ℂ, (starRingEnd ℂ) z = z →
              Even (u.count z) := by
            intro z hz
            exact even_residual_count020 t (K.1 + L.1) u hdec z
              (hfix z hz) (hcfixed z hz)
          obtain ⟨q, hqu, hqj, hqi⟩ :=
            ih u.card hcard u rfl hustar huneg hui hufix
          refine ⟨K.1 + q, ?_, ?_, ?_⟩
          · calc
              t = (K.1 + L.1) + u := hdec
              _ = (K.1 + L.1) +
                  (q + Multiset.map (starRingEnd ℂ) q) := by rw [hqu]
              _ = (K.1 + q) +
                  Multiset.map (starRingEnd ℂ) (K.1 + q) := by
                rw [Multiset.map_add]
                rw [hLval]
                ac_rfl
          · rw [Multiset.map_add, hKj, hqj]
          · rw [Multiset.map_add, hKi, hqi]
        · have hinter : ∃ z, z ∈ K ∧ z ∈ L := by
            by_contra hno
            apply hdisj
            refine Finset.disjoint_left.mpr ?_
            intro z hzK hzL
            exact hno ⟨z, hzK, hzL⟩
          have hstarA0 : (starRingEnd ℂ) a ∈ orbitFin020 a := by
            exact star_mem_of_orbit_intersection020 a (by
              simpa [K, L] using hinter)
          have hKLfin : L = K := by
            simpa [K, L] using
              orbitStarFin020_eq_orbit_of_overlap020 a hstarA0
          have hKLval : L.1 = K.1 := congrArg (fun F : Finset ℂ => F.1) hKLfin
          have hstarK : Multiset.map (starRingEnd ℂ) K.1 = K.1 := by
            exact hLval.symm.trans hKLval
          have hKfixed : ∀ z ∈ K, (starRingEnd ℂ) z = z := by
            simpa [K] using star_fixed_on_orbit_of_overlap020 a hstarA0
          have hdouble : K.1 + K.1 ≤ t := by
            exact finset_double_val_le_of_even020 t K hKmem
              (fun z hz => hfix z (hKfixed z hz))
          have hdouble_ne : K.1 + K.1 ≠ 0 := by
            intro hz
            have haz : a ∈ K.1 + K.1 := by simp [haK]
            rw [hz] at haz
            simp at haz
          let u : Multiset ℂ := t - (K.1 + K.1)
          have hdec : t = (K.1 + K.1) + u := by
            dsimp [u]
            exact residual_decomposition020 t (K.1 + K.1) hdouble
          have hlt : u < t := by
            dsimp [u]
            exact residual_lt020 t (K.1 + K.1) hdouble hdouble_ne
          have hcard : u.card < n := by
            have hc : u.card < t.card := Multiset.card_lt_card hlt
            exact hc.trans_eq ht
          have hdoublej : Multiset.map starNegMap020 (K.1 + K.1) =
              K.1 + K.1 := by rw [Multiset.map_add, hKj]
          have hdoublei : Multiset.map invStar127 (K.1 + K.1) =
              K.1 + K.1 := by rw [Multiset.map_add, hKi]
          have hdoubleStar : Multiset.map (starRingEnd ℂ) (K.1 + K.1) =
              K.1 + K.1 := by rw [Multiset.map_add, hstarK]
          have hdoubleNeg : Multiset.map (fun z : ℂ => -z) (K.1 + K.1) =
              K.1 + K.1 := by
            rw [show (fun z : ℂ => -z) =
                starNegMap020 ∘ (starRingEnd ℂ) by
                  funext z
                  simp [starNegMap020]]
            rw [← Multiset.map_map, hdoubleStar, hdoublej]
          have hustar : Multiset.map (starRingEnd ℂ) u = u := by
            dsimp [u]
            exact residual_invariant020 t (K.1 + K.1) hdouble
              (starRingEnd ℂ) hst hdoubleStar
          have huj : Multiset.map starNegMap020 u = u := by
            dsimp [u]
            exact residual_invariant020 t (K.1 + K.1) hdouble
              starNegMap020 hj hdoublej
          have hui : Multiset.map invStar127 u = u := by
            dsimp [u]
            exact residual_invariant020 t (K.1 + K.1) hdouble
              invStar127 hiv hdoublei
          have huneg : Multiset.map (fun z : ℂ => -z) u = u := by
            dsimp [u]
            exact residual_invariant020 t (K.1 + K.1) hdouble
              (fun z : ℂ => -z) hng hdoubleNeg
          have hufix : ∀ z : ℂ, (starRingEnd ℂ) z = z →
              Even (u.count z) := by
            intro z hz
            exact even_residual_count020 t (K.1 + K.1) u hdec z
              (hfix z hz) (by
                simp only [Multiset.count_add]
                exact even_double_finset_count020 K z)
          obtain ⟨q, hqu, hqj, hqi⟩ :=
            ih u.card hcard u rfl hustar huneg hui hufix
          refine ⟨K.1 + q, ?_, ?_, ?_⟩
          · calc
              t = (K.1 + K.1) + u := hdec
              _ = (K.1 + K.1) +
                  (q + Multiset.map (starRingEnd ℂ) q) := by rw [hqu]
              _ = (K.1 + q) +
                  Multiset.map (starRingEnd ℂ) (K.1 + q) := by
                rw [Multiset.map_add, hstarK]
                ac_rfl
          · rw [Multiset.map_add, hKj, hqj]
          · rw [Multiset.map_add, hKi, hqi]
  exact hP s.card s rfl hstar hneg hinv hfixed

/-! ## Cayley root partition with the reciprocal involution -/

theorem cayley_root_partition_with_inv020
    (input : GeneralRealQSPPolynomial127) :
    ∃ q : Multiset ℂ,
      ((cayleyNumerator127 (intervalResidual127 input)
          (2 * input.degree)).map Complex.ofRealHom).roots =
        q + Multiset.map (starRingEnd ℂ) q ∧
      Multiset.map starNegMap020 q = q ∧
      Multiset.map invStar127 q = q := by
  let p : Polynomial ℝ := cayleyNumerator127 (intervalResidual127 input)
      (2 * input.degree)
  have hd : (intervalResidual127 input).natDegree ≤ 2 * input.degree :=
    intervalResidual127_natDegree_le_twice127 input
  have hnonneg : ∀ x : ℝ, -1 ≤ x → x ≤ 1 →
      0 ≤ Polynomial.eval x (intervalResidual127 input) := by
    intro x hxlo hxhi
    exact intervalResidual127_nonnegative input hxlo hxhi
  by_cases hzero : p = 0
  · refine ⟨0, ?_, by simp, by simp⟩
    simp [p, hzero]
  · have hpmap : p.map Complex.ofRealHom ≠ 0 := by
      intro hpmapzero
      apply hzero
      exact (Polynomial.map_eq_zero_iff Complex.ofRealHom.injective).mp hpmapzero
    apply exists_star_neg_inv_half020
    · exact complexified_roots_star_closed127 p
    · exact complexified_cayley_roots_neg_closed127
        (intervalResidual127 input) (2 * input.degree) hd
    · change Multiset.map (fun z : ℂ => ((starRingEnd ℂ) z)⁻¹)
          (p.map Complex.ofRealHom).roots =
          (p.map Complex.ofRealHom).roots
      simpa [p] using cayleyNumerator127_roots_invStar_fixed127 input
    · intro z hzfix
      rw [Polynomial.count_roots]
      by_cases hzroot : (p.map Complex.ofRealHom).IsRoot z
      · exact complexified_rootMultiplicity_even_of_nonnegative_global127
          p hzero (cayley_nonnegative127
            (intervalResidual127 input) (2 * input.degree) hd hnonneg)
          hzroot hzfix
      · have hnotpos : ¬ 0 < (p.map Complex.ofRealHom).rootMultiplicity z := by
          intro hpos
          apply hzroot
          exact (Polynomial.rootMultiplicity_pos hpmap).mp hpos
        have hmul : (p.map Complex.ofRealHom).rootMultiplicity z = 0 := by
          omega
        rw [hmul]
        exact ⟨0, by simp⟩

/-! ## Fixed-width zero-root balance for reciprocal factors -/

theorem reflect_fixed_zero_balance021
    (p : Polynomial ℂ) (N : ℕ) (hp : p ≠ 0)
    (hdeg : p.natDegree ≤ N) (hfix : p.reflect N = p) :
    p.rootMultiplicity 0 + p.natDegree = N := by
  obtain ⟨q, hpq, hqnot⟩ :=
    p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp 0
  have hpq' : p =
      (Polynomial.X : Polynomial ℂ) ^ p.rootMultiplicity 0 * q := by
    simpa using hpq
  have hq0 : q ≠ 0 := by
    intro hq0
    apply hp
    rw [hpq, hq0, mul_zero]
  have hnotX : ¬ Polynomial.X ∣ q := by
    intro hX
    apply hqnot
    simpa using hX
  have hqcoeff0 : q.coeff 0 ≠ 0 := by
    exact (Polynomial.X_dvd_iff.not).mp hnotX
  have hmuldeg :
      p.natDegree = p.rootMultiplicity 0 + q.natDegree := by
    have hmuldeg0 := congrArg Polynomial.natDegree hpq'
    calc
      p.natDegree =
          (((Polynomial.X : Polynomial ℂ) ^ p.rootMultiplicity 0 * q).natDegree) := by
            exact hmuldeg0
      _ = p.rootMultiplicity 0 + q.natDegree := by
            rw [Polynomial.natDegree_mul]
            · simp
            · exact pow_ne_zero _ (Polynomial.X_ne_zero)
            · exact hq0
  have hqdeg : q.natDegree ≤ N - p.rootMultiplicity 0 := by
    omega
  have hm : p.rootMultiplicity 0 ≤ N := by
    omega
  have hreflect :
      p = Polynomial.reflect (p.rootMultiplicity 0)
            ((Polynomial.X : Polynomial ℂ) ^ p.rootMultiplicity 0) *
              q.reflect (N - p.rootMultiplicity 0) := by
    calc
      p = p.reflect N := hfix.symm
      _ = (((Polynomial.X : Polynomial ℂ) ^ p.rootMultiplicity 0) * q).reflect N := by
            exact congrArg (fun r : Polynomial ℂ => r.reflect N) hpq'
      _ = Polynomial.reflect (p.rootMultiplicity 0)
            ((Polynomial.X : Polynomial ℂ) ^ p.rootMultiplicity 0) *
              q.reflect (N - p.rootMultiplicity 0) := by
            have hrm := Polynomial.reflect_mul
              (F := p.rootMultiplicity 0) (G := N - p.rootMultiplicity 0)
              ((Polynomial.X : Polynomial ℂ) ^ p.rootMultiplicity 0) q
              (by simp) hqdeg
            have hwidth : p.rootMultiplicity 0 +
                (N - p.rootMultiplicity 0) = N := by omega
            rw [hwidth] at hrm
            exact hrm
  have hreflectX :
      Polynomial.reflect (p.rootMultiplicity 0)
          ((Polynomial.X : Polynomial ℂ) ^ p.rootMultiplicity 0) = 1 := by
    rw [Polynomial.reflect_monomial, Polynomial.revAt_le le_rfl]
    simp
  rw [hreflectX] at hreflect
  have hdegqref :
      (q.reflect (N - p.rootMultiplicity 0)).natDegree =
        N - p.rootMultiplicity 0 := by
    apply le_antisymm
    · calc
        (q.reflect (N - p.rootMultiplicity 0)).natDegree ≤
            max (N - p.rootMultiplicity 0) q.natDegree :=
          Polynomial.natDegree_reflect_le
        _ = N - p.rootMultiplicity 0 := max_eq_left hqdeg
    · apply Polynomial.le_natDegree_of_ne_zero
      rw [Polynomial.coeff_reflect, Polynomial.revAt_le le_rfl]
      simpa using hqcoeff0
  have hdegp :
      p.natDegree = N - p.rootMultiplicity 0 := by
    have hdegp0 := congrArg Polynomial.natDegree hreflect
    simpa [hdegqref] using hdegp0
  omega

lemma count_star_zero021 (q : Multiset ℂ) :
    (Multiset.map (starRingEnd ℂ) q).count 0 = q.count 0 := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons a q ih =>
      simp only [Multiset.map_cons, Multiset.count_cons]
      rw [ih]
      by_cases ha : (0 : ℂ) = a
      · subst a
        simp
      · have hsa : ¬(0 : ℂ) = (starRingEnd ℂ) a := by
          intro h
          apply ha
          have h' := congrArg (starRingEnd ℂ) h
          simpa using h'
        simp [ha, hsa]

theorem cayley_q_zero_balance021
    (input : GeneralRealQSPPolynomial127) {q : Multiset ℂ}
    (hp : (cayleyResidualComplex127 input) ≠ 0)
    (hroots : (cayleyResidualComplex127 input).roots =
      q + Multiset.map (starRingEnd ℂ) q) :
    q.card + q.count 0 = 2 * input.degree := by
  let P : Polynomial ℂ := cayleyResidualComplex127 input
  have hPdeg : P.natDegree ≤ 4 * input.degree := by
    dsimp [P, cayleyResidualComplex127]
    rw [Polynomial.natDegree_map_eq_of_injective Complex.ofRealHom.injective]
    exact cayleyResidual127_natDegree_le127 input
  have hPfix : P.reflect (4 * input.degree) = P := by
    exact cayleyResidualComplex127_reflect_fixed127 input
  have hbalance := reflect_fixed_zero_balance021 P (4 * input.degree) hp hPdeg hPfix
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hcard : P.natDegree = P.roots.card :=
    hsplit.natDegree_eq_card_roots
  have hrootcard : P.roots.card = q.card + q.card := by
    rw [hroots]
    simp
  have hzero_count : P.roots.count 0 = 2 * q.count 0 := by
    have hroots' : P.roots = q + Multiset.map (starRingEnd ℂ) q := by
      simpa [P] using hroots
    rw [hroots']
    rw [Multiset.count_add, count_star_zero021]
    omega
  have hzero : P.rootMultiplicity 0 = 2 * q.count 0 := by
    rw [← Polynomial.count_roots]
    exact hzero_count
  omega

/-! ## Unit phase normalization for reciprocal spectral factors -/

/-! ## Unit root products and the reflected spectral-factor coefficient -/

noncomputable def nonzeroProduct022 (s : Multiset ℂ) : ℂ :=
  (s.filter (fun z : ℂ => z ≠ 0)).prod

lemma card_filter_ne_zero_add_count_zero022 (s : Multiset ℂ) :
    (s.filter (fun z : ℂ => z ≠ 0)).card + s.count 0 = s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      simp only [Multiset.filter_cons, Multiset.card_cons,
        Multiset.count_cons]
      by_cases ha : a = 0
      · subst a
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          congrArg (fun n : ℕ => n + 1) ih
      · simp [ha, Ne.symm ha]
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          congrArg (fun n : ℕ => n + 1) ih

lemma rootProduct_cons022 (a : ℂ) (s : Multiset ℂ) :
    rootProduct127 (a ::ₘ s) =
      ((Polynomial.X : Polynomial ℂ) - Polynomial.C a) *
        rootProduct127 s := by
  simp [rootProduct127]

lemma prod_map_invStar022 (s : Multiset ℂ) :
    (s.map invStar127).prod =
      ((starRingEnd ℂ) s.prod)⁻¹ := by
  induction s using Multiset.induction_on with
  | empty => simp [invStar127]
  | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [ih]
      simp only [invStar127, map_mul]
      ring

lemma prod_ne_zero022 (s : Multiset ℂ)
    (hs : ∀ z ∈ s, z ≠ 0) : s.prod ≠ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      simp only [Multiset.prod_cons]
      apply mul_ne_zero
      · exact hs a (by simp)
      · apply ih
        intro z hz
        exact hs z (by simp [hz])

lemma nonzero_filter_invStar022 (s : Multiset ℂ) :
    (s.map invStar127).filter (fun z : ℂ => z ≠ 0) =
      (s.filter (fun z : ℂ => z ≠ 0)).map invStar127 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.filter_cons]
      by_cases ha : a = 0
      · subst a
        simp [invStar127, ih]
      · have hia : invStar127 a ≠ 0 := by
          simp [invStar127, ha]
        simp [ha, hia, ih]

lemma nonzero_filter_starNeg022 (s : Multiset ℂ) :
    (s.map starNegMap020).filter (fun z : ℂ => z ≠ 0) =
      (s.filter (fun z : ℂ => z ≠ 0)).map starNegMap020 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.filter_cons]
      by_cases ha : a = 0
      · subst a
        simp [starNegMap020, ih]
      · have hia : starNegMap020 a ≠ 0 := by
          simp [starNegMap020, ha]
        simp [ha, ih]

lemma prod_map_starNeg022 (s : Multiset ℂ) :
    (s.map starNegMap020).prod =
      (-1 : ℂ) ^ s.card * (starRingEnd ℂ) s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp [starNegMap020]
  | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
      rw [ih]
      simp only [starNegMap020, map_mul]
      rw [pow_succ]
      ring

noncomputable def reflectCoeff022 (s : Multiset ℂ) : ℂ :=
  (-1 : ℂ) ^ (s.filter (fun z : ℂ => z ≠ 0)).card *
    nonzeroProduct022 s

theorem nonzeroProduct_unit022
    (s : Multiset ℂ) (hmap : s.map invStar127 = s) :
    Complex.normSq (nonzeroProduct022 s) = 1 := by
  let t : Multiset ℂ := s.filter (fun z : ℂ => z ≠ 0)
  let r : ℂ := t.prod
  have htmap : t = t.map invStar127 := by
    calc
      t = (s.map invStar127).filter (fun z : ℂ => z ≠ 0) := by
        rw [hmap]
      _ = (s.filter (fun z : ℂ => z ≠ 0)).map invStar127 :=
        nonzero_filter_invStar022 s
  have hprod : r = (t.map invStar127).prod := by
    dsimp [r]
    exact congrArg Multiset.prod htmap
  have hr : r = ((starRingEnd ℂ) r)⁻¹ := by
    calc
      r = (t.map invStar127).prod := hprod
      _ = ((starRingEnd ℂ) r)⁻¹ := by
        simpa [r] using prod_map_invStar022 t
  have htne : ∀ z ∈ t, z ≠ 0 := by
    intro z hz
    exact (Multiset.mem_filter.mp hz).2
  have hrne : r ≠ 0 := by
    exact prod_ne_zero022 t htne
  have hstarne : (starRingEnd ℂ) r ≠ 0 := by
    intro h
    apply hrne
    have h' := congrArg (starRingEnd ℂ) h
    simpa using h'
  have hunit : r * (starRingEnd ℂ) r = 1 := by
    calc
      r * (starRingEnd ℂ) r =
          ((starRingEnd ℂ) r)⁻¹ * (starRingEnd ℂ) r :=
            congrArg (fun z => z * (starRingEnd ℂ) r) hr
      _ = 1 := inv_mul_cancel₀ hstarne
  have hnormC : (Complex.normSq r : ℂ) = 1 := by
    calc
      (Complex.normSq r : ℂ) = r * (starRingEnd ℂ) r :=
        (Complex.mul_conj r).symm
      _ = 1 := hunit
  have hnormR := congrArg Complex.re hnormC
  have hnorm : Complex.normSq r = 1 := by simpa using hnormR
  simpa [r, t, nonzeroProduct022] using hnorm

theorem reflectCoeff_unit022
    (s : Multiset ℂ) (hmap : s.map invStar127 = s) :
    Complex.normSq (reflectCoeff022 s) = 1 := by
  have hfilterunit : Complex.normSq (nonzeroProduct022 s) = 1 :=
    nonzeroProduct_unit022 s hmap
  have hsign : Complex.normSq
      ((-1 : ℂ) ^ (s.filter (fun z : ℂ => z ≠ 0)).card) = 1 := by
    induction (s.filter (fun z : ℂ => z ≠ 0)).card with
    | zero => norm_num
    | succ n ih =>
        rw [pow_succ, Complex.normSq_mul, ih]
        norm_num
  dsimp [reflectCoeff022]
  rw [Complex.normSq_mul, hsign, hfilterunit]
  norm_num

theorem reflectCoeff_real022
    (s : Multiset ℂ) (d : ℕ)
    (hneg : s.map starNegMap020 = s)
    (hwidth : s.card + s.count 0 = 2 * d) :
    (starRingEnd ℂ) (reflectCoeff022 s) = reflectCoeff022 s := by
  have hcard := card_filter_ne_zero_add_count_zero022 s
  have heven : Even (s.filter (fun z : ℂ => z ≠ 0)).card := by
    rcases Nat.even_or_odd (s.filter (fun z : ℂ => z ≠ 0)).card with he | ho
    · exact he
    · rcases ho with ⟨k, hk⟩
      exfalso
      omega
  have hsign : (-1 : ℂ) ^ (s.filter (fun z : ℂ => z ≠ 0)).card = 1 := by
    rcases heven with ⟨k, hk⟩
    rw [hk]
    simp
  let t : Multiset ℂ := s.filter (fun z : ℂ => z ≠ 0)
  let r : ℂ := t.prod
  have htmap : t = t.map starNegMap020 := by
    calc
      t = (s.map starNegMap020).filter (fun z : ℂ => z ≠ 0) := by
        rw [hneg]
      _ = (s.filter (fun z : ℂ => z ≠ 0)).map starNegMap020 :=
        nonzero_filter_starNeg022 s
  have hprod : r = (t.map starNegMap020).prod := by
    dsimp [r]
    exact congrArg Multiset.prod htmap
  have hrel : r = (-1 : ℂ) ^ t.card * (starRingEnd ℂ) r := by
    calc
      r = (t.map starNegMap020).prod := hprod
      _ = (-1 : ℂ) ^ t.card * (starRingEnd ℂ) t.prod :=
        prod_map_starNeg022 t
      _ = (-1 : ℂ) ^ t.card * (starRingEnd ℂ) r := by rfl
  have hrealr : (starRingEnd ℂ) r = r := by
    have hrel' : r = (starRingEnd ℂ) r := by
      simpa [t, hsign] using hrel
    exact hrel'.symm
  have hnr : (starRingEnd ℂ) (nonzeroProduct022 s) =
      nonzeroProduct022 s := by
    simpa [nonzeroProduct022, r, t] using hrealr
  change (starRingEnd ℂ)
      (((-1 : ℂ) ^ (s.filter (fun z : ℂ => z ≠ 0)).card) *
        nonzeroProduct022 s) =
    ((-1 : ℂ) ^ (s.filter (fun z : ℂ => z ≠ 0)).card) *
      nonzeroProduct022 s
  rw [map_mul, hsign, hnr]
  simp

theorem rootProduct_reflect_with_zeros022
    (s : Multiset ℂ) :
    (rootProduct127 s).reflect (s.card + s.count 0) =
      Polynomial.C ((-1 : ℂ) ^ (s.filter (fun z : ℂ => z ≠ 0)).card *
        nonzeroProduct022 s) *
        rootProduct127 (s.map (fun z : ℂ => z⁻¹)) := by
  induction s using Multiset.induction_on with
  | empty => simp [rootProduct127, nonzeroProduct022]
  | cons a s ih =>
      by_cases ha : a = 0
      · subst a
        have hroot := rootProduct_cons022 0 s
        have hrootinv := rootProduct_cons022 (0⁻¹)
            (s.map (fun z : ℂ => z⁻¹))
        rw [show (0 ::ₘ s).map (fun z : ℂ => z⁻¹) =
            0⁻¹ ::ₘ s.map (fun z : ℂ => z⁻¹) by simp]
        rw [hroot, hrootinv]
        have hcount : Multiset.count 0 (0 ::ₘ s) = s.count 0 + 1 := by
          simp
        rw [hcount]
        simp [nonzeroProduct022]
        rw [show s.card + 1 + (s.count 0 + 1) =
            1 + ((s.card + s.count 0) + 1) by omega]
        rw [Polynomial.reflect_mul
          (F := 1) (G := s.card + s.count 0 + 1)
          (Polynomial.X : Polynomial ℂ) (rootProduct127 s) (by simp) (by
            exact (rootProduct_natDegree_le127 s).trans (by omega))]
        have hpad : (rootProduct127 s).reflect
              (s.card + s.count 0 + 1) =
            (rootProduct127 s).reflect (s.card + s.count 0) *
              (Polynomial.X : Polynomial ℂ) := by
          have hpad' := Polynomial.reflect_mul
            (F := s.card + s.count 0) (G := 1)
            (rootProduct127 s) (1 : Polynomial ℂ)
            ((rootProduct_natDegree_le127 s).trans (by omega)) (by simp)
          simpa [Polynomial.reflect_C, mul_comm] using hpad'
        rw [hpad, ih]
        simp [nonzeroProduct022]
        ring
      · have hsa : a ≠ 0 := ha
        have hroot := rootProduct_cons022 a s
        have hrootinv := rootProduct_cons022 a⁻¹
            (s.map (fun z : ℂ => z⁻¹))
        rw [show (a ::ₘ s).map (fun z : ℂ => z⁻¹) =
            a⁻¹ ::ₘ s.map (fun z : ℂ => z⁻¹) by simp]
        rw [hroot, hrootinv]
        have hcount : Multiset.count 0 (a ::ₘ s) = s.count 0 := by
          simp [Ne.symm ha]
        rw [hcount]
        simp [nonzeroProduct022, ha]
        rw [show s.card + 1 + s.count 0 =
            1 + (s.card + s.count 0) by omega]
        rw [Polynomial.reflect_mul
          (F := 1) (G := s.card + s.count 0)
          ((Polynomial.X : Polynomial ℂ) - Polynomial.C a)
          (rootProduct127 s) (by simp) (by
            exact (rootProduct_natDegree_le127 s).trans (by omega))]
        rw [reflect_linear_to_inverse127 a hsa, ih]
        simp [nonzeroProduct022]
        rw [pow_succ]
        ring

lemma map_star_eq_map_inv022 (s : Multiset ℂ)
    (hmap : s.map invStar127 = s) :
    s.map (starRingEnd ℂ) = s.map (fun z : ℂ => z⁻¹) := by
  have h := congrArg (Multiset.map (fun z : ℂ => z⁻¹)) hmap
  simpa [Multiset.map_map, Function.comp_def, invStar127] using h

theorem spectralFactor_reflect_unit022
    (p : Polynomial ℝ) (N : ℕ) {q : Multiset ℂ}
    (hwidth : q.card + q.count 0 = N)
    (hmap : q.map invStar127 = q) :
    ∃ c : ℂ, c = reflectCoeff022 q ∧ Complex.normSq c = 1 ∧
      (spectralFactor127 p q).reflect N =
        Polynomial.C c *
          (spectralFactor127 p q).map (starRingEnd ℂ) := by
  have hfilterunit :
      Complex.normSq (nonzeroProduct022 q) = 1 :=
    nonzeroProduct_unit022 q hmap
  let c : ℂ := reflectCoeff022 q
  have hsign : Complex.normSq
      ((-1 : ℂ) ^ (q.filter (fun z : ℂ => z ≠ 0)).card) = 1 := by
    induction (q.filter (fun z : ℂ => z ≠ 0)).card with
    | zero => norm_num
    | succ n ih =>
        rw [pow_succ, Complex.normSq_mul, ih]
        norm_num
  have hc : Complex.normSq c = 1 := by
    dsimp [c, reflectCoeff022]
    rw [Complex.normSq_mul, hsign, hfilterunit]
    norm_num
  have hroot :
      (rootProduct127 q).reflect (q.card + q.count 0) =
        Polynomial.C c * rootProduct127
          (q.map (fun z : ℂ => z⁻¹)) := by
    simpa [c, reflectCoeff022] using rootProduct_reflect_with_zeros022 q
  have hrootmap : rootProduct127
      (q.map (fun z : ℂ => z⁻¹)) =
      (rootProduct127 q).map (starRingEnd ℂ) := by
    rw [rootProduct_star_map127]
    congr 1
    exact (map_star_eq_map_inv022 q hmap).symm
  have href := Polynomial.reflect_mul
      (F := 0) (G := q.card + q.count 0)
      (Polynomial.C (Real.sqrt p.leadingCoeff : ℂ))
      (rootProduct127 q) (by simp)
      ((rootProduct_natDegree_le127 q).trans (by omega))
  rw [show 0 + (q.card + q.count 0) = N by omega] at href
  have hstarcoeff :
      (starRingEnd ℂ) (Real.sqrt p.leadingCoeff : ℂ) =
        (Real.sqrt p.leadingCoeff : ℂ) := by simp
  refine ⟨c, by rfl, hc, ?_⟩
  change (Polynomial.C (Real.sqrt p.leadingCoeff : ℂ) * rootProduct127 q).reflect N =
    Polynomial.C c *
      (Polynomial.C (Real.sqrt p.leadingCoeff : ℂ) * rootProduct127 q).map
        (starRingEnd ℂ)
  rw [href, Polynomial.reflect_C, hroot, hrootmap]
  rw [Polynomial.map_mul, Polynomial.map_C, hstarcoeff]
  ring

lemma realPart_coeff022 (Q : Polynomial ℂ) (n : ℕ) :
    (realPartPolynomial127 Q).coeff n = (Q.coeff n).re := by
  rfl

lemma imagPart_coeff022 (Q : Polynomial ℂ) (n : ℕ) :
    (imagPartPolynomial127 Q).coeff n = (Q.coeff n).im := by
  rfl

lemma realPart_reflect022 (Q : Polynomial ℂ) (N : ℕ) :
    realPartPolynomial127 (Q.reflect N) =
      (realPartPolynomial127 Q).reflect N := by
  apply Polynomial.ext
  intro n
  simp only [realPart_coeff022, Polynomial.coeff_reflect]

lemma imagPart_reflect022 (Q : Polynomial ℂ) (N : ℕ) :
    imagPartPolynomial127 (Q.reflect N) =
      (imagPartPolynomial127 Q).reflect N := by
  apply Polynomial.ext
  intro n
  simp only [imagPart_coeff022, Polynomial.coeff_reflect]

lemma realPart_C_mul_map_star022 (s : ℂ) (Q : Polynomial ℂ)
    (hs : (starRingEnd ℂ) s = s) :
    realPartPolynomial127 (Polynomial.C s * Q.map (starRingEnd ℂ)) =
      Polynomial.C s.re * realPartPolynomial127 Q := by
  apply Polynomial.ext
  intro n
  simp only [realPart_coeff022, Polynomial.coeff_C_mul,
    Polynomial.coeff_map]
  rw [Complex.mul_re]
  have him : s.im = 0 := by
    have h := congrArg Complex.im hs
    have h' : -s.im = s.im := by simpa [Complex.star_def] using h
    linarith
  simp [him]

lemma imagPart_C_mul_map_star022 (s : ℂ) (Q : Polynomial ℂ)
    (hs : (starRingEnd ℂ) s = s) :
    imagPartPolynomial127 (Polynomial.C s * Q.map (starRingEnd ℂ)) =
      Polynomial.C (-s.re) * imagPartPolynomial127 Q := by
  apply Polynomial.ext
  intro n
  simp only [imagPart_coeff022, Polynomial.coeff_C_mul,
    Polynomial.coeff_map]
  rw [Complex.mul_im]
  have him : s.im = 0 := by
    have h := congrArg Complex.im hs
    have h' : -s.im = s.im := by simpa [Complex.star_def] using h
    linarith
  simp [him]

lemma unit_sign_real022 (d : ℕ) :
    (starRingEnd ℂ) ((-1 : ℂ) ^ d) = (-1 : ℂ) ^ d := by
  induction d with
  | zero => norm_num
  | succ d ih =>
      rw [pow_succ, map_mul, ih]
      norm_num

lemma unit_sign_re022 (d : ℕ) :
    (((-1 : ℂ) ^ d).re) = (-1 : ℝ) ^ d := by
  induction d with
  | zero => norm_num
  | succ d ih =>
      simp [pow_succ, ih]

/-! ## Symmetric spectral factors for the Cayley polynomial -/

lemma rootProduct_neg_map020
    (s : Multiset ℂ) :
    rootProduct127 (s.map (fun z : ℂ => -z)) =
      Polynomial.C ((-1 : ℂ) ^ s.card) *
        (rootProduct127 s).comp (-(Polynomial.X : Polynomial ℂ)) := by
  induction s using Multiset.induction_on with
  | empty => simp [rootProduct127]
  | cons a s ih =>
      simp only [rootProduct127, Multiset.map_cons, Multiset.prod_cons,
        Multiset.card_cons]
      change ((Polynomial.X : Polynomial ℂ) - Polynomial.C (-a)) *
          rootProduct127 (s.map (fun z : ℂ => -z)) =
        Polynomial.C ((-1 : ℂ) ^ (Multiset.card s + 1)) *
          (((Polynomial.X : Polynomial ℂ) - Polynomial.C a) *
            rootProduct127 s).comp (-(Polynomial.X : Polynomial ℂ))
      rw [ih]
      simp
      rw [pow_succ]
      ring

lemma spectral_factor_neg_conjugacy020
    (p : Polynomial ℝ) (q : Multiset ℂ)
    (hqj : Multiset.map (fun z : ℂ => -(starRingEnd ℂ) z) q = q) :
    (spectralFactor127 p q).map (starRingEnd ℂ) =
      Polynomial.C ((-1 : ℂ) ^ q.card) *
        (spectralFactor127 p q).comp (-(Polynomial.X : Polynomial ℂ)) := by
  have hstarneg : Multiset.map (starRingEnd ℂ) q =
      Multiset.map (fun z : ℂ => -z) q := by
    have h := congrArg (Multiset.map (starRingEnd ℂ)) hqj
    simpa [Multiset.map_map, Function.comp_def] using h.symm
  have hroot : rootProduct127 (q.map (starRingEnd ℂ)) =
      rootProduct127 (q.map (fun z : ℂ => -z)) := by
    rw [hstarneg]
  have hroot' : rootProduct127 (q.map star) =
      rootProduct127 (q.map (fun z : ℂ => -z)) := by
    change rootProduct127 (q.map (starRingEnd ℂ)) =
      rootProduct127 (q.map (fun z : ℂ => -z))
    exact hroot
  unfold spectralFactor127
  rw [Polynomial.map_mul, Polynomial.map_C, rootProduct_star_map127,
    hroot', rootProduct_neg_map020]
  simp
  ring

lemma eval_map_real020 (a : Polynomial ℝ) (x : ℝ) :
    Polynomial.eval (x : ℂ) (a.map Complex.ofRealHom) =
      ((Polynomial.eval x a : ℝ) : ℂ) := by
  calc
    Polynomial.eval (x : ℂ) (a.map Complex.ofRealHom) =
        Polynomial.eval₂ Complex.ofRealHom (x : ℂ) a :=
      Polynomial.eval_map Complex.ofRealHom (x : ℂ)
    _ = Complex.ofRealHom (Polynomial.eval x a) := by
      simpa using (Polynomial.eval₂_at_apply Complex.ofRealHom x (p := a))
    _ = ((Polynomial.eval x a : ℝ) : ℂ) := rfl

lemma spectral_factor_eval_parity_even020
    (p : Polynomial ℝ) (q : Multiset ℂ)
    (hqj : Multiset.map (fun z : ℂ => -(starRingEnd ℂ) z) q = q)
    (hcard : Even q.card) :
    ∀ x : ℝ,
      Polynomial.eval (-x)
          (realPartPolynomial127 (spectralFactor127 p q)) =
        Polynomial.eval x
          (realPartPolynomial127 (spectralFactor127 p q)) ∧
      Polynomial.eval (-x)
          (imagPartPolynomial127 (spectralFactor127 p q)) =
        -Polynomial.eval x
          (imagPartPolynomial127 (spectralFactor127 p q)) := by
  intro x
  let Q : Polynomial ℂ := spectralFactor127 p q
  let A : Polynomial ℝ := realPartPolynomial127 Q
  let B : Polynomial ℝ := imagPartPolynomial127 Q
  have hQ := spectral_factor_neg_conjugacy020 p q hqj
  have hsign : (-1 : ℂ) ^ q.card = 1 := by
    rcases hcard with ⟨m, hm⟩
    rw [hm]
    simp
  have hsym : Q.map (starRingEnd ℂ) =
      Q.comp (-(Polynomial.X : Polynomial ℂ)) := by
    simpa [Q, hsign] using hQ
  have hstarDec := polynomial_star_decomposition127 Q
  have hdec := polynomial_coeff_decomposition127 Q
  have hleft : Polynomial.eval (x : ℂ) (Q.map (starRingEnd ℂ)) =
      ((Polynomial.eval x A : ℝ) : ℂ) -
        Complex.I * ((Polynomial.eval x B : ℝ) : ℂ) := by
    rw [hstarDec]
    simp [A, B, eval_map_real020]
  have hright : Polynomial.eval (x : ℂ)
      (Q.comp (-(Polynomial.X : Polynomial ℂ))) =
      ((Polynomial.eval (-x) A : ℝ) : ℂ) +
        Complex.I * ((Polynomial.eval (-x) B : ℝ) : ℂ) := by
    calc
      Polynomial.eval (x : ℂ)
          (Q.comp (-(Polynomial.X : Polynomial ℂ))) =
          Polynomial.eval (-x : ℂ) Q := by
            rw [Polynomial.eval_comp]
            simp
      _ = Polynomial.eval (-x : ℂ)
          (A.map Complex.ofRealHom +
            Polynomial.C Complex.I * B.map Complex.ofRealHom) := by
            rw [hdec]
      _ = ((Polynomial.eval (-x) A : ℝ) : ℂ) +
          Complex.I * ((Polynomial.eval (-x) B : ℝ) : ℂ) := by
            rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
            have hAneg : Polynomial.eval (- (x : ℂ))
                (A.map Complex.ofRealHom) =
                ((Polynomial.eval (-x) A : ℝ) : ℂ) := by
              calc
                Polynomial.eval (- (x : ℂ)) (A.map Complex.ofRealHom) =
                    Polynomial.eval ((-x : ℝ) : ℂ)
                      (A.map Complex.ofRealHom) := by simp
                _ = ((Polynomial.eval (-x) A : ℝ) : ℂ) :=
                  eval_map_real020 A (-x)
            have hBneg : Polynomial.eval (- (x : ℂ))
                (B.map Complex.ofRealHom) =
                ((Polynomial.eval (-x) B : ℝ) : ℂ) := by
              calc
                Polynomial.eval (- (x : ℂ)) (B.map Complex.ofRealHom) =
                    Polynomial.eval ((-x : ℝ) : ℂ)
                      (B.map Complex.ofRealHom) := by simp
                _ = ((Polynomial.eval (-x) B : ℝ) : ℂ) :=
                  eval_map_real020 B (-x)
            rw [hAneg, hBneg]
  have hpoint :
      ((Polynomial.eval x A : ℝ) : ℂ) -
          Complex.I * ((Polynomial.eval x B : ℝ) : ℂ) =
        ((Polynomial.eval (-x) A : ℝ) : ℂ) +
          Complex.I * ((Polynomial.eval (-x) B : ℝ) : ℂ) := by
    exact hleft.symm.trans (hsym ▸ hright)
  have hreal := congrArg Complex.re hpoint
  have himag := congrArg Complex.im hpoint
  constructor
  · simpa using hreal.symm
  · simpa using himag.symm

lemma spectral_factor_eval_parity_odd020
    (p : Polynomial ℝ) (q : Multiset ℂ)
    (hqj : Multiset.map (fun z : ℂ => -(starRingEnd ℂ) z) q = q)
    (hcard : Odd q.card) :
    ∀ x : ℝ,
      Polynomial.eval (-x)
          (realPartPolynomial127 (spectralFactor127 p q)) =
        -Polynomial.eval x
          (realPartPolynomial127 (spectralFactor127 p q)) ∧
      Polynomial.eval (-x)
          (imagPartPolynomial127 (spectralFactor127 p q)) =
        Polynomial.eval x
          (imagPartPolynomial127 (spectralFactor127 p q)) := by
  intro x
  let Q : Polynomial ℂ := spectralFactor127 p q
  let A : Polynomial ℝ := realPartPolynomial127 Q
  let B : Polynomial ℝ := imagPartPolynomial127 Q
  have hQ := spectral_factor_neg_conjugacy020 p q hqj
  have hsign : (-1 : ℂ) ^ q.card = -1 := by
    rcases hcard with ⟨m, hm⟩
    rw [hm]
    norm_num [pow_add]
  have hsym : Q.map (starRingEnd ℂ) =
      -(Q.comp (-(Polynomial.X : Polynomial ℂ))) := by
    simpa [Q, hsign] using hQ
  have hstarDec := polynomial_star_decomposition127 Q
  have hdec := polynomial_coeff_decomposition127 Q
  have hleft : Polynomial.eval (x : ℂ) (Q.map (starRingEnd ℂ)) =
      ((Polynomial.eval x A : ℝ) : ℂ) -
        Complex.I * ((Polynomial.eval x B : ℝ) : ℂ) := by
    rw [hstarDec]
    simp [A, B, eval_map_real020]
  have hright : Polynomial.eval (x : ℂ)
      (Q.comp (-(Polynomial.X : Polynomial ℂ))) =
      ((Polynomial.eval (-x) A : ℝ) : ℂ) +
        Complex.I * ((Polynomial.eval (-x) B : ℝ) : ℂ) := by
    calc
      Polynomial.eval (x : ℂ)
          (Q.comp (-(Polynomial.X : Polynomial ℂ))) =
          Polynomial.eval (-x : ℂ) Q := by
            rw [Polynomial.eval_comp]
            simp
      _ = Polynomial.eval (-x : ℂ)
          (A.map Complex.ofRealHom +
            Polynomial.C Complex.I * B.map Complex.ofRealHom) := by
            rw [hdec]
      _ = ((Polynomial.eval (-x) A : ℝ) : ℂ) +
          Complex.I * ((Polynomial.eval (-x) B : ℝ) : ℂ) := by
            rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
            have hAneg : Polynomial.eval (- (x : ℂ))
                (A.map Complex.ofRealHom) =
                ((Polynomial.eval (-x) A : ℝ) : ℂ) := by
              calc
                Polynomial.eval (- (x : ℂ)) (A.map Complex.ofRealHom) =
                    Polynomial.eval ((-x : ℝ) : ℂ)
                      (A.map Complex.ofRealHom) := by simp
                _ = ((Polynomial.eval (-x) A : ℝ) : ℂ) :=
                  eval_map_real020 A (-x)
            have hBneg : Polynomial.eval (- (x : ℂ))
                (B.map Complex.ofRealHom) =
                ((Polynomial.eval (-x) B : ℝ) : ℂ) := by
              calc
                Polynomial.eval (- (x : ℂ)) (B.map Complex.ofRealHom) =
                    Polynomial.eval ((-x : ℝ) : ℂ)
                      (B.map Complex.ofRealHom) := by simp
                _ = ((Polynomial.eval (-x) B : ℝ) : ℂ) :=
                  eval_map_real020 B (-x)
            rw [hAneg, hBneg]
  have hpoint :
      ((Polynomial.eval x A : ℝ) : ℂ) -
          Complex.I * ((Polynomial.eval x B : ℝ) : ℂ) =
        - (((Polynomial.eval (-x) A : ℝ) : ℂ) +
          Complex.I * ((Polynomial.eval (-x) B : ℝ) : ℂ)) := by
    have hrightneg : Polynomial.eval (x : ℂ)
        (-(Q.comp (-(Polynomial.X : Polynomial ℂ)))) =
        - (((Polynomial.eval (-x) A : ℝ) : ℂ) +
          Complex.I * ((Polynomial.eval (-x) B : ℝ) : ℂ)) := by
      simpa only [Polynomial.eval_neg] using
        congrArg (fun z : ℂ => -z) hright
    exact hleft.symm.trans (hsym ▸ hrightneg)
  have hreal := congrArg Complex.re hpoint
  have himag := congrArg Complex.im hpoint
  have hreal' : Polynomial.eval x A =
      -Polynomial.eval (-x) A := by
    simpa using hreal
  have himag' : -Polynomial.eval x B =
      -Polynomial.eval (-x) B := by
    simpa using himag
  constructor
  · linarith [hreal']
  · linarith [himag']

/-! ## Even polynomials and the inverse Cayley transform -/

theorem coeff_comp_neg_X020 (p : Polynomial ℝ) (n : ℕ) :
    (p.comp (-(Polynomial.X : Polynomial ℝ))).coeff n =
      (-1 : ℝ) ^ n * p.coeff n := by
  have hpow (m : ℕ) :
      (-(Polynomial.X : Polynomial ℝ)) ^ m =
        (-1 : Polynomial ℝ) ^ m * Polynomial.X ^ m := by
    exact neg_pow _ _
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [hp, hq]
      ring
  | monomial m a =>
      by_cases h : n = m
      · subst n
        simp [Polynomial.comp, hpow]
        have hminus : (-1 : Polynomial ℝ) = Polynomial.C (-1) := by
          norm_num
        rw [hminus, ← Polynomial.C_pow, Polynomial.coeff_C_mul]
        simp
        ring
      · simp [Polynomial.comp, hpow]
        have hminus : (-1 : Polynomial ℝ) = Polynomial.C (-1) := by
          norm_num
        rw [hminus, ← Polynomial.C_pow, Polynomial.coeff_C_mul]
        have h' : ¬m = n := by
          intro hmn
          exact h hmn.symm
        rw [Polynomial.coeff_monomial]
        simp [Polynomial.coeff_X_pow, h, h']

theorem even_coeff_zero020
    (p : Polynomial ℝ)
    (heven : p.comp (-(Polynomial.X : Polynomial ℝ)) = p)
    {n : ℕ} (hn : ¬ 2 ∣ n) : p.coeff n = 0 := by
  have hc := congrArg (fun r : Polynomial ℝ => r.coeff n) heven
  rw [coeff_comp_neg_X020] at hc
  have hodd : (-1 : ℝ) ^ n = -1 := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact (hn ⟨k, by omega⟩).elim
    · rw [hk]
      norm_num [pow_add]
  rw [hodd] at hc
  linarith

theorem expand_contract_even020
    (p : Polynomial ℝ) (n : ℕ)
    (_hdeg : p.natDegree ≤ 2 * n)
    (heven : p.comp (-(Polynomial.X : Polynomial ℝ)) = p) :
    p = Polynomial.expand ℝ 2 (Polynomial.contract 2 p) := by
  apply Polynomial.ext
  intro k
  by_cases hk : 2 ∣ k
  · obtain ⟨j, rfl⟩ := hk
    rw [Polynomial.coeff_expand]
    · rw [Polynomial.coeff_contract]
      · simp [Nat.mul_comm]
      · norm_num
    · norm_num
  · have hodd := even_coeff_zero020 p heven hk
    rw [Polynomial.coeff_expand]
    · simp [hk, hodd]
    · norm_num

theorem contract_degree_le020
    (p : Polynomial ℝ) (d : ℕ)
    (hp : p.degree ≤ (2 * d : WithBot ℕ)) :
    (Polynomial.contract 2 p).degree ≤ (d : WithBot ℕ) := by
  rw [Polynomial.degree_le_iff_coeff_zero]
  intro m hm
  rw [Polynomial.coeff_contract (by norm_num)]
  apply (Polynomial.degree_le_iff_coeff_zero p (2 * d : WithBot ℕ)).mp hp
  have hm' : d < m := by
    exact_mod_cast hm
  have hmul : 2 * d < m * 2 := by omega
  exact_mod_cast hmul

theorem odd_coeff_zero_even020
    (p : Polynomial ℝ)
    (hodd : p.comp (-(Polynomial.X : Polynomial ℝ)) = -p)
    {n : ℕ} (hn : 2 ∣ n) : p.coeff n = 0 := by
  have hc := congrArg (fun r : Polynomial ℝ => r.coeff n) hodd
  rw [coeff_comp_neg_X020] at hc
  have hpow : (-1 : ℝ) ^ n = 1 := by
    obtain ⟨k, hk⟩ := hn
    rw [hk]
    simp
  rw [hpow] at hc
  simp at hc
  linarith

theorem odd_div_X_even020
    (O : Polynomial ℝ) (d : ℕ) (hdpos : 0 < d)
    (hdeg : O.degree ≤ (2 * d : WithBot ℕ))
    (hodd_eval : ∀ x : ℝ,
      Polynomial.eval (-x) O = -Polynomial.eval x O) :
    ∃ u : Polynomial ℝ,
      O = Polynomial.X * u ∧
      u.comp (-(Polynomial.X : Polynomial ℝ)) = u ∧
      u.degree ≤ ((2 * (d - 1) : ℕ) : WithBot ℕ) := by
  have hodd_comp : O.comp (-(Polynomial.X : Polynomial ℝ)) = -O := by
    apply Polynomial.funext
    intro x
    rw [Polynomial.eval_comp]
    simpa using hodd_eval x
  have hcoeff0 : O.coeff 0 = 0 := by
    have h0 := hodd_eval 0
    have heval0 : Polynomial.eval 0 O = 0 := by
      have h0' : Polynomial.eval 0 O = -Polynomial.eval 0 O := by
        simpa using h0
      linarith
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact heval0
  have hroot : O.IsRoot 0 :=
    (Polynomial.zero_isRoot_iff_coeff_zero_eq_zero).2 hcoeff0
  let u : Polynomial ℝ := O /ₘ Polynomial.X
  have hmul : Polynomial.X * u = O := by
    have hmul' :=
      (Polynomial.mul_divByMonic_eq_iff_isRoot
        (p := O) (a := (0 : ℝ))).2 hroot
    simpa [u] using hmul'
  have htransfer :
      (-(Polynomial.X : Polynomial ℝ)) * u.comp
          (-(Polynomial.X : Polynomial ℝ)) =
        (-(Polynomial.X : Polynomial ℝ)) * u := by
    calc
      (-(Polynomial.X : Polynomial ℝ)) * u.comp
          (-(Polynomial.X : Polynomial ℝ)) =
          (Polynomial.X * u).comp
            (-(Polynomial.X : Polynomial ℝ)) := by
              rw [Polynomial.mul_comp]
              simp
      _ = O.comp (-(Polynomial.X : Polynomial ℝ)) := by rw [hmul]
      _ = -O := hodd_comp
      _ = -(Polynomial.X * u) := by rw [hmul]
      _ = (-(Polynomial.X : Polynomial ℝ)) * u := by ring
  have hueven : u.comp (-(Polynomial.X : Polynomial ℝ)) = u := by
    apply mul_left_cancel₀
      (show (-(Polynomial.X : Polynomial ℝ)) ≠ 0 by
        exact neg_ne_zero.mpr Polynomial.X_ne_zero)
    exact htransfer
  have hudeg : u.degree ≤ ((2 * (d - 1) : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_le_iff_coeff_zero]
    intro m hm
    have hm' : 2 * (d - 1) < m := by
      exact_mod_cast hm
    have hcoeff : u.coeff m = O.coeff (m + 1) := by
      have hc := congrArg (fun r : Polynomial ℝ => r.coeff (m + 1)) hmul
      simpa [Polynomial.coeff_X_mul] using hc
    rw [hcoeff]
    by_cases hlarge : 2 * d < m + 1
    · apply (Polynomial.degree_le_iff_coeff_zero O (2 * d : WithBot ℕ)).mp hdeg
      exact_mod_cast hlarge
    · have heq : m + 1 = 2 * d := by omega
      rw [heq]
      apply odd_coeff_zero_even020 O hodd_comp
      exact ⟨d, by omega⟩
  exact ⟨u, hmul.symm, hueven, hudeg⟩

/-! ## The explicit inverse Cayley transform -/

def cayleyLeftHalf020 : Polynomial ℝ :=
  Polynomial.C (1 / 2 : ℝ) * ((1 : Polynomial ℝ) - Polynomial.X)

def cayleyRightHalf020 : Polynomial ℝ :=
  Polynomial.C (1 / 2 : ℝ) * ((1 : Polynomial ℝ) + Polynomial.X)

def inverseCayley020 (e : Polynomial ℝ) (d : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (d + 1),
    Polynomial.C (e.coeff i) *
      (cayleyLeftHalf020 ^ i * cayleyRightHalf020 ^ (d - i))

theorem cayleyLeftHalf_degree020 :
    cayleyLeftHalf020.degree ≤ (1 : WithBot ℕ) := by
  unfold cayleyLeftHalf020
  calc
    (Polynomial.C (1 / 2 : ℝ) *
        ((1 : Polynomial ℝ) - Polynomial.X)).degree ≤
      (Polynomial.C (1 / 2 : ℝ)).degree +
        ((1 : Polynomial ℝ) - Polynomial.X).degree :=
      Polynomial.degree_mul_le _ _
    _ ≤ (0 : WithBot ℕ) + (1 : WithBot ℕ) := by
      apply add_le_add
      · exact Polynomial.degree_C_le
      · apply (Polynomial.degree_sub_le _ _).trans
        exact max_le_max Polynomial.degree_one_le Polynomial.degree_X_le
    _ ≤ (1 : WithBot ℕ) := by simp

theorem cayleyRightHalf_degree020 :
    cayleyRightHalf020.degree ≤ (1 : WithBot ℕ) := by
  unfold cayleyRightHalf020
  calc
    (Polynomial.C (1 / 2 : ℝ) *
        ((1 : Polynomial ℝ) + Polynomial.X)).degree ≤
      (Polynomial.C (1 / 2 : ℝ)).degree +
        ((1 : Polynomial ℝ) + Polynomial.X).degree :=
      Polynomial.degree_mul_le _ _
    _ ≤ (0 : WithBot ℕ) + (1 : WithBot ℕ) := by
      apply add_le_add
      · exact Polynomial.degree_C_le
      · apply (Polynomial.degree_add_le _ _).trans
        exact max_le_max Polynomial.degree_one_le Polynomial.degree_X_le
    _ ≤ (1 : WithBot ℕ) := by simp

theorem inverseCayley_degree020
    (e : Polynomial ℝ) (d : ℕ) :
    (inverseCayley020 e d).degree ≤ (d : WithBot ℕ) := by
  unfold inverseCayley020
  apply (Polynomial.degree_sum_le (Finset.range (d + 1))
    (fun i => Polynomial.C (e.coeff i) *
      (cayleyLeftHalf020 ^ i * cayleyRightHalf020 ^ (d - i)))).trans
  apply Finset.sup_le
  intro i hi
  calc
    (Polynomial.C (e.coeff i) *
        (cayleyLeftHalf020 ^ i * cayleyRightHalf020 ^ (d - i))).degree ≤
      (Polynomial.C (e.coeff i)).degree +
        (cayleyLeftHalf020 ^ i * cayleyRightHalf020 ^ (d - i)).degree :=
      Polynomial.degree_mul_le _ _
    _ ≤ (0 : WithBot ℕ) +
        (i • (1 : WithBot ℕ) +
          (d - i : ℕ) • (1 : WithBot ℕ)) := by
      apply add_le_add
      · exact Polynomial.degree_C_le
      · apply (Polynomial.degree_mul_le _ _).trans
        apply add_le_add
        · apply (Polynomial.degree_pow_le _ _).trans
          exact nsmul_le_nsmul_right cayleyLeftHalf_degree020 _
        · apply (Polynomial.degree_pow_le _ _).trans
          exact nsmul_le_nsmul_right cayleyRightHalf_degree020 _
    _ ≤ (d : WithBot ℕ) := by
      have hi_le : i ≤ d := by
        exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      simp only [zero_add, nsmul_eq_mul, mul_one]
      exact_mod_cast (show i + (d - i) ≤ d by omega)

theorem inverseCayley_eval020
    (e : Polynomial ℝ) (d : ℕ) (he : e.natDegree ≤ d) (t : ℝ) :
    Polynomial.eval ((1 - t ^ 2) / (1 + t ^ 2))
        (inverseCayley020 e d) * (1 + t ^ 2) ^ d =
      Polynomial.eval (t ^ 2) e := by
  let x : ℝ := (1 - t ^ 2) / (1 + t ^ 2)
  have hden : (1 + t ^ 2 : ℝ) ≠ 0 := by
    nlinarith [sq_nonneg t]
  have hleft : Polynomial.eval x cayleyLeftHalf020 =
      t ^ 2 / (1 + t ^ 2) := by
    dsimp [x, cayleyLeftHalf020]
    simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_one]
    field_simp
    ring
  have hright : Polynomial.eval x cayleyRightHalf020 =
      1 / (1 + t ^ 2) := by
    dsimp [x, cayleyRightHalf020]
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_one]
    field_simp
    ring
  rw [show Polynomial.eval ((1 - t ^ 2) / (1 + t ^ 2))
      (inverseCayley020 e d) = Polynomial.eval x
        (inverseCayley020 e d) by rfl]
  unfold inverseCayley020
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow]
  rw [hleft, hright]
  rw [Finset.sum_mul]
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr he)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ d := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hsum : i + (d - i) = d := Nat.add_sub_of_le hi_le
  simp only [div_pow, one_div]
  have hinvpow :
      (1 + t ^ 2)⁻¹ ^ (d - i) * (1 + t ^ 2) ^ d =
        (1 + t ^ 2) ^ i := by
    have haux :
        (1 + t ^ 2)⁻¹ ^ (d - i) *
            (1 + t ^ 2) ^ (i + (d - i)) =
          (1 + t ^ 2) ^ i := by
      rw [inv_pow, pow_add]
      field_simp [hden]
    simpa [hsum] using haux
  have hterm :
      ((t ^ 2) ^ i / (1 + t ^ 2) ^ i *
          (1 + t ^ 2)⁻¹ ^ (d - i)) *
          (1 + t ^ 2) ^ d = (t ^ 2) ^ i := by
    calc
      ((t ^ 2) ^ i / (1 + t ^ 2) ^ i *
          (1 + t ^ 2)⁻¹ ^ (d - i)) *
          (1 + t ^ 2) ^ d =
        ((t ^ 2) ^ i / (1 + t ^ 2) ^ i) *
          ((1 + t ^ 2)⁻¹ ^ (d - i) *
            (1 + t ^ 2) ^ d) := by ring
      _ = ((t ^ 2) ^ i / (1 + t ^ 2) ^ i) *
          (1 + t ^ 2) ^ i := by rw [hinvpow]
      _ = (t ^ 2) ^ i := by field_simp [hden]
  calc
    e.coeff i * ((t ^ 2) ^ i / (1 + t ^ 2) ^ i *
        (1 + t ^ 2)⁻¹ ^ (d - i)) * (1 + t ^ 2) ^ d =
      e.coeff i * (((t ^ 2) ^ i / (1 + t ^ 2) ^ i *
        (1 + t ^ 2)⁻¹ ^ (d - i)) * (1 + t ^ 2) ^ d) := by ring
    _ = e.coeff i * (t ^ 2) ^ i := by rw [hterm]

theorem inverseCayley_cayley_eq020
    (e : Polynomial ℝ) (d : ℕ) (he : e.natDegree ≤ d) :
    cayleyNumerator127 (inverseCayley020 e d) d =
      Polynomial.expand ℝ 2 e := by
  apply Polynomial.funext
  intro t
  rw [cayley_eval_homogenized127 _ _
    (Polynomial.natDegree_le_iff_degree_le.mpr
      (inverseCayley_degree020 e d))]
  rw [Polynomial.expand_eval]
  exact inverseCayley_eval020 e d he t

theorem cayleyNumerator_injective020
    (r s : Polynomial ℝ) (d : ℕ)
    (hr : r.natDegree ≤ d) (hs : s.natDegree ≤ d)
    (h : cayleyNumerator127 r d = cayleyNumerator127 s d) :
    r = s := by
  apply Polynomial.eq_of_infinite_eval_eq r s
  refine (Set.Ioo_infinite (show (-1 : ℝ) < 1 by norm_num)).mono ?_
  intro x hx
  let t : ℝ := Real.sqrt ((1 - x) / (1 + x))
  have hdenx : 0 < (1 + x : ℝ) := by linarith [hx.1]
  have hnumx : 0 ≤ (1 - x : ℝ) := by linarith [hx.2]
  have ht2 : t ^ 2 = (1 - x) / (1 + x) := by
    dsimp [t]
    exact Real.sq_sqrt (div_nonneg hnumx hdenx.le)
  have hmap : (1 - t ^ 2) / (1 + t ^ 2) = x := by
    rw [ht2]
    field_simp [ne_of_gt hdenx]
    ring
  have he := congrArg (fun z : Polynomial ℝ => Polynomial.eval t z) h
  rw [cayley_eval_homogenized127 r d hr t,
    cayley_eval_homogenized127 s d hs t] at he
  rw [hmap] at he
  apply mul_right_cancel₀
  · have hdenT : 0 < (1 + t ^ 2 : ℝ) := by
      nlinarith [sq_nonneg t]
    exact pow_ne_zero d (ne_of_gt hdenT)
  · exact he

theorem cayleyNumerator_sq020
    (B : Polynomial ℝ) (d : ℕ) (hB : B.natDegree ≤ d) :
    cayleyNumerator127 (B ^ 2) (2 * d) =
      (cayleyNumerator127 B d) ^ 2 := by
  have hBsq : (B ^ 2).natDegree ≤ 2 * d := by
    calc
      (B ^ 2).natDegree ≤ 2 * B.natDegree :=
        Polynomial.natDegree_pow_le
      _ ≤ 2 * d := Nat.mul_le_mul_left 2 hB
  apply Polynomial.funext
  intro t
  rw [cayley_eval_homogenized127 (B ^ 2) (2 * d) hBsq t]
  simp only [Polynomial.eval_pow]
  rw [cayley_eval_homogenized127 B d hB t]
  ring

theorem cayleyNumerator_interval_sq020
    (C : Polynomial ℝ) (d : ℕ) (hd : 0 < d)
    (hC : C.natDegree ≤ d - 1) :
    cayleyNumerator127
        (((1 : Polynomial ℝ) - Polynomial.X ^ 2) * C ^ 2)
        (2 * d) =
      (Polynomial.C (2 : ℝ) * Polynomial.X *
        cayleyNumerator127 C (d - 1)) ^ 2 := by
  have hleft :
      ((1 : Polynomial ℝ) - Polynomial.X ^ 2).natDegree ≤ 2 := by
    calc
      ((1 : Polynomial ℝ) - Polynomial.X ^ 2).natDegree ≤
          max (1 : Polynomial ℝ).natDegree (Polynomial.X ^ 2).natDegree :=
        Polynomial.natDegree_sub_le _ _
      _ = 2 := by simp
  have hCsq : (C ^ 2).natDegree ≤ 2 * (d - 1) := by
    calc
      (C ^ 2).natDegree ≤ 2 * C.natDegree :=
        Polynomial.natDegree_pow_le
      _ ≤ 2 * (d - 1) := Nat.mul_le_mul_left 2 hC
  have hterm :
      (((1 : Polynomial ℝ) - Polynomial.X ^ 2) * C ^ 2).natDegree ≤
        2 * d := by
    calc
      (((1 : Polynomial ℝ) - Polynomial.X ^ 2) * C ^ 2).natDegree ≤
          ((1 : Polynomial ℝ) - Polynomial.X ^ 2).natDegree +
            (C ^ 2).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 2 + 2 * (d - 1) := add_le_add hleft hCsq
      _ = 2 * d := by omega
  apply Polynomial.funext
  intro t
  let x : ℝ := (1 - t ^ 2) / (1 + t ^ 2)
  have hden : (1 + t ^ 2 : ℝ) ≠ 0 := by
    nlinarith [sq_nonneg t]
  have hscale (z : ℝ) :
      (1 - x ^ 2) * z ^ 2 * (1 + t ^ 2) ^ (2 * d) =
        (2 * t * (z * (1 + t ^ 2) ^ (d - 1))) ^ 2 := by
    have hdecomp : 2 * d = 2 + 2 * (d - 1) := by omega
    dsimp [x]
    rw [hdecomp, pow_add]
    field_simp [hden]
    ring
  calc
    Polynomial.eval t
        (cayleyNumerator127
          (((1 : Polynomial ℝ) - Polynomial.X ^ 2) * C ^ 2)
          (2 * d)) =
        Polynomial.eval x
          (((1 : Polynomial ℝ) - Polynomial.X ^ 2) * C ^ 2) *
          (1 + t ^ 2) ^ (2 * d) := by
            rw [cayley_eval_homogenized127 _ _ hterm t]
    _ = (2 * t *
          (Polynomial.eval x C * (1 + t ^ 2) ^ (d - 1))) ^ 2 := by
            simp only [Polynomial.eval_mul, Polynomial.eval_sub,
              Polynomial.eval_one, Polynomial.eval_pow,
              Polynomial.eval_X]
            exact hscale (Polynomial.eval x C)
    _ = Polynomial.eval t
        ((Polynomial.C (2 : ℝ) * Polynomial.X *
          cayleyNumerator127 C (d - 1)) ^ 2) := by
            rw [Polynomial.eval_pow, Polynomial.eval_mul,
              Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
              cayley_eval_homogenized127 C (d - 1) hC t]

theorem cayleyNumerator_add020
    (r s : Polynomial ℝ) (d : ℕ)
    (hr : r.natDegree ≤ d) (hs : s.natDegree ≤ d) :
    cayleyNumerator127 (r + s) d =
      cayleyNumerator127 r d + cayleyNumerator127 s d := by
  have hsumdeg : (r + s).natDegree ≤ d := by
    calc
      (r + s).natDegree ≤ max r.natDegree s.natDegree :=
        Polynomial.natDegree_add_le r s
      _ ≤ d := max_le hr hs
  apply Polynomial.funext
  intro t
  rw [cayley_eval_homogenized127 (r + s) d hsumdeg t]
  rw [Polynomial.eval_add]
  rw [Polynomial.eval_add]
  rw [cayley_eval_homogenized127 r d hr t,
    cayley_eval_homogenized127 s d hs t]
  ring

theorem cayleyNumerator_decomposition020
    (B C : Polynomial ℝ) (d : ℕ) (hd : 0 < d)
    (hB : B.natDegree ≤ d) (hC : C.natDegree ≤ d - 1) :
    cayleyNumerator127
        (B ^ 2 + ((1 : Polynomial ℝ) - Polynomial.X ^ 2) * C ^ 2)
        (2 * d) =
      (cayleyNumerator127 B d) ^ 2 +
        (Polynomial.C (2 : ℝ) * Polynomial.X *
          cayleyNumerator127 C (d - 1)) ^ 2 := by
  have hBsq : (B ^ 2).natDegree ≤ 2 * d := by
    calc
      (B ^ 2).natDegree ≤ 2 * B.natDegree :=
        Polynomial.natDegree_pow_le
      _ ≤ 2 * d := Nat.mul_le_mul_left 2 hB
  have hleft :
      ((1 : Polynomial ℝ) - Polynomial.X ^ 2).natDegree ≤ 2 := by
    calc
      ((1 : Polynomial ℝ) - Polynomial.X ^ 2).natDegree ≤
          max (1 : Polynomial ℝ).natDegree (Polynomial.X ^ 2).natDegree :=
        Polynomial.natDegree_sub_le _ _
      _ = 2 := by simp
  have hCsq : (C ^ 2).natDegree ≤ 2 * (d - 1) := by
    calc
      (C ^ 2).natDegree ≤ 2 * C.natDegree :=
        Polynomial.natDegree_pow_le
      _ ≤ 2 * (d - 1) := Nat.mul_le_mul_left 2 hC
  have hterm :
      (((1 : Polynomial ℝ) - Polynomial.X ^ 2) * C ^ 2).natDegree ≤
        2 * d := by
    calc
      (((1 : Polynomial ℝ) - Polynomial.X ^ 2) * C ^ 2).natDegree ≤
          ((1 : Polynomial ℝ) - Polynomial.X ^ 2).natDegree +
            (C ^ 2).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 2 + 2 * (d - 1) := add_le_add hleft hCsq
      _ = 2 * d := by omega
  calc
    cayleyNumerator127
        (B ^ 2 + ((1 : Polynomial ℝ) - Polynomial.X ^ 2) * C ^ 2)
        (2 * d) =
        cayleyNumerator127 (B ^ 2) (2 * d) +
          cayleyNumerator127
            (((1 : Polynomial ℝ) - Polynomial.X ^ 2) * C ^ 2) (2 * d) := by
              exact cayleyNumerator_add020 (B ^ 2)
                (((1 : Polynomial ℝ) - Polynomial.X ^ 2) * C ^ 2)
                (2 * d) hBsq hterm
    _ = (cayleyNumerator127 B d) ^ 2 +
          (Polynomial.C (2 : ℝ) * Polynomial.X *
            cayleyNumerator127 C (d - 1)) ^ 2 := by
              rw [cayleyNumerator_sq020 B d hB,
                cayleyNumerator_interval_sq020 C d hd hC]

/-! ## Parity-aware factors of the Cayley residual

The spectral factor supplied by the accepted global two-square layer has a
fixed star/negation symmetry.  Splitting its real and imaginary parts gives
the two parity alternatives; the following theorem records that split with
the degree bound needed by the inverse Cayley step. -/

theorem even_inverse_cayley020
    (E : Polynomial ℝ) (d : ℕ)
    (hdeg : E.degree ≤ (2 * d : WithBot ℕ))
    (heven : ∀ x : ℝ, Polynomial.eval (-x) E = Polynomial.eval x E) :
    ∃ B : Polynomial ℝ,
      cayleyNumerator127 B d = E ∧
      B.degree ≤ (d : WithBot ℕ) := by
  have hnat : E.natDegree ≤ 2 * d :=
    (Polynomial.natDegree_le_iff_degree_le).mpr hdeg
  let e : Polynomial ℝ := Polynomial.contract 2 E
  have heven_comp : E.comp (-(Polynomial.X : Polynomial ℝ)) = E := by
    apply Polynomial.funext
    intro x
    rw [Polynomial.eval_comp]
    simpa using heven x
  have heq : E = Polynomial.expand ℝ 2 e := by
    exact expand_contract_even020 E d hnat heven_comp
  have hedeg : e.degree ≤ (d : WithBot ℕ) := by
    exact contract_degree_le020 E d hdeg
  have henat : e.natDegree ≤ d :=
    (Polynomial.natDegree_le_iff_degree_le).mpr hedeg
  let B : Polynomial ℝ := inverseCayley020 e d
  have hbridge := inverseCayley_cayley_eq020 e d henat
  refine ⟨B, ?_, ?_⟩
  · exact hbridge.trans heq.symm
  · exact inverseCayley_degree020 e d

theorem odd_inverse_cayley020
    (O : Polynomial ℝ) (d : ℕ) (hdpos : 0 < d)
    (hdeg : O.degree ≤ (2 * d : WithBot ℕ))
    (hodd : ∀ x : ℝ,
      Polynomial.eval (-x) O = -Polynomial.eval x O) :
    ∃ C : Polynomial ℝ,
      O = Polynomial.C (2 : ℝ) * Polynomial.X *
        cayleyNumerator127 C (d - 1) ∧
      C.degree ≤ ((d - 1 : ℕ) : WithBot ℕ) := by
  obtain ⟨u, hOu, hueven, hudeg⟩ :=
    odd_div_X_even020 O d hdpos hdeg hodd
  have hunat : u.natDegree ≤ 2 * (d - 1) :=
    (Polynomial.natDegree_le_iff_degree_le).mpr hudeg
  let h0 : Polynomial ℝ := Polynomial.contract 2 u
  have h0deg : h0.degree ≤ ((d - 1 : ℕ) : WithBot ℕ) := by
    exact contract_degree_le020 u (d - 1) hudeg
  have h0nat : h0.natDegree ≤ d - 1 :=
    (Polynomial.natDegree_le_iff_degree_le).mpr h0deg
  have hu_expand : u = Polynomial.expand ℝ 2 h0 := by
    exact expand_contract_even020 u (d - 1) hunat hueven
  let hhalf : Polynomial ℝ := Polynomial.C (1 / 2 : ℝ) * h0
  have hhalf_nat : hhalf.natDegree ≤ d - 1 := by
    dsimp [hhalf]
    calc
      (Polynomial.C (1 / 2 : ℝ) * h0).natDegree ≤
          (Polynomial.C (1 / 2 : ℝ)).natDegree + h0.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ d - 1 := by simpa using h0nat
  let C : Polynomial ℝ := inverseCayley020 hhalf (d - 1)
  have hCeq : cayleyNumerator127 C (d - 1) =
      Polynomial.expand ℝ 2 hhalf := by
    exact inverseCayley_cayley_eq020 hhalf (d - 1) hhalf_nat
  have hhalf_expand : Polynomial.expand ℝ 2 hhalf =
      Polynomial.C (1 / 2 : ℝ) * u := by
    calc
      Polynomial.expand ℝ 2 hhalf =
          Polynomial.C (1 / 2 : ℝ) *
            Polynomial.expand ℝ 2 h0 := by
              simp [hhalf, Polynomial.expand_eq_comp_X_pow,
                Polynomial.mul_comp]
      _ = Polynomial.C (1 / 2 : ℝ) * u := by rw [hu_expand]
  have hCdeg_le : C.degree ≤ ((d - 1 : ℕ) : WithBot ℕ) := by
    exact inverseCayley_degree020 hhalf (d - 1)
  refine ⟨C, ?_, hCdeg_le⟩
  calc
    O = Polynomial.X * u := hOu
    _ = Polynomial.C (2 : ℝ) * Polynomial.X *
          (Polynomial.C (1 / 2 : ℝ) * u) := by
            have hC : Polynomial.C (2 : ℝ) *
                Polynomial.C (1 / 2 : ℝ) =
                (1 : Polynomial ℝ) := by
              rw [← Polynomial.C_mul]
              norm_num
            calc
              Polynomial.X * u =
                  (1 : Polynomial ℝ) * (Polynomial.X * u) := by simp
              _ = (Polynomial.C (2 : ℝ) *
                  Polynomial.C (1 / 2 : ℝ)) *
                    (Polynomial.X * u) := by rw [hC]
              _ = Polynomial.C (2 : ℝ) * Polynomial.X *
                  (Polynomial.C (1 / 2 : ℝ) * u) := by ring
    _ = Polynomial.C (2 : ℝ) * Polynomial.X *
          Polynomial.expand ℝ 2 hhalf := by rw [hhalf_expand]
    _ = Polynomial.C (2 : ℝ) * Polynomial.X *
          cayleyNumerator127 C (d - 1) := by rw [hCeq]

/-! ## A sign-targeted component bridge for an oriented root half

The ordinary star-negation symmetry determines which real component is even
and which is odd.  The reflected coefficient is kept as a separate input to
this bridge: this is the exact algebraic condition that a root-orbit
orientation must provide. -/

theorem spectralFactor_targeted_components023
    (p : Polynomial ℝ) (d : ℕ) (hp : p ≠ 0)
    (hlead : 0 ≤ p.leadingCoeff) {q : Multiset ℂ}
    (hwidth : q.card + q.count 0 = 2 * d)
    (hpartition : (p.map Complex.ofRealHom).roots =
      q + Multiset.map (starRingEnd ℂ) q)
    (hqj : Multiset.map starNegMap020 q = q)
    (hqi : Multiset.map invStar127 q = q)
    (htarget : reflectCoeff022 q =
      (-1 : ℂ) ^ (d + q.card)) :
    ∃ E O : Polynomial ℝ,
      p = E ^ 2 + O ^ 2 ∧
      (∀ x : ℝ, Polynomial.eval (-x) E = Polynomial.eval x E) ∧
      (∀ x : ℝ, Polynomial.eval (-x) O = -Polynomial.eval x O) ∧
      E.reflect (2 * d) =
        Polynomial.C ((-1 : ℝ) ^ d) * E ∧
      O.reflect (2 * d) =
        Polynomial.C (-((-1 : ℝ) ^ d)) * O ∧
      E.degree ≤ (2 * d : WithBot ℕ) ∧
      O.degree ≤ (2 * d : WithBot ℕ) := by
  let Q : Polynomial ℂ := spectralFactor127 p q
  let A : Polynomial ℝ := realPartPolynomial127 Q
  let B : Polynomial ℝ := imagPartPolynomial127 Q
  have hfactor : p.map Complex.ofRealHom = Q * Q.map (starRingEnd ℂ) := by
    exact complex_spectral_factor_of_root_partition127
      p hp hlead hpartition
  have hsum : p = A ^ 2 + B ^ 2 := by
    have hreal := real_two_squares_of_complex_factor127 p Q hfactor
    simpa [Q, A, B] using hreal
  have hQdeg : Q.natDegree ≤ q.card := by
    exact spectralFactor_natDegree_le127 p q
  have hqdeg : q.card ≤ 2 * d := by
    omega
  have hAdeg : A.degree ≤ (2 * d : WithBot ℕ) := by
    have hAnat : A.natDegree ≤ 2 * d := by
      exact (realPart_natDegree_le127 Q).trans
        (hQdeg.trans hqdeg)
    exact (Polynomial.natDegree_le_iff_degree_le).mp hAnat
  have hBdeg : B.degree ≤ (2 * d : WithBot ℕ) := by
    have hBnat : B.natDegree ≤ 2 * d := by
      exact (imagPart_natDegree_le127 Q).trans
        (hQdeg.trans hqdeg)
    exact (Polynomial.natDegree_le_iff_degree_le).mp hBnat
  obtain ⟨c, hc, hcnorm, hreflect⟩ :=
    spectralFactor_reflect_unit022 p (2 * d) hwidth hqi
  have hreflect' : Q.reflect (2 * d) =
      Polynomial.C ((-1 : ℂ) ^ (d + q.card)) *
        Q.map (starRingEnd ℂ) := by
    rw [hc, htarget] at hreflect
    simpa [Q] using hreflect
  have hsstar : (starRingEnd ℂ) ((-1 : ℂ) ^ (d + q.card)) =
      (-1 : ℂ) ^ (d + q.card) :=
    unit_sign_real022 (d + q.card)
  have hA := congrArg realPartPolynomial127 hreflect'
  have hB := congrArg imagPartPolynomial127 hreflect'
  rw [realPart_reflect022,
    realPart_C_mul_map_star022 _ _ hsstar,
    unit_sign_re022] at hA
  rw [imagPart_reflect022,
    imagPart_C_mul_map_star022 _ _ hsstar,
    unit_sign_re022] at hB
  have hA' : A.reflect (2 * d) =
      Polynomial.C ((-1 : ℝ) ^ (d + q.card)) * A := by
    simpa [A, Q] using hA
  have hB' : B.reflect (2 * d) =
      Polynomial.C (-((-1 : ℝ) ^ (d + q.card))) * B := by
    simpa [B, Q] using hB
  have hqpar : q.card % 2 = 0 ∨ q.card % 2 = 1 := by omega
  rcases hqpar with hqeven | hqodd
  · have hqeven' : Even q.card := by
      exact Nat.even_iff.mpr hqeven
    have hpar := spectral_factor_eval_parity_even020 p q hqj hqeven'
    have hsign : (-1 : ℝ) ^ (d + q.card) = (-1 : ℝ) ^ d := by
      rw [pow_add]
      have hpow : (-1 : ℝ) ^ q.card = 1 := by
        rcases hqeven' with ⟨m, hm⟩
        rw [hm]
        simp
      rw [hpow]
      ring
    refine ⟨A, B, hsum, ?_, ?_, ?_, ?_, hAdeg, hBdeg⟩
    · intro x
      exact (hpar x).1
    · intro x
      exact (hpar x).2
    · simpa [hsign] using hA'
    · simpa [hsign] using hB'
  · have hqodd' : Odd q.card := by
      exact Nat.odd_iff.mpr hqodd
    have hpar := spectral_factor_eval_parity_odd020 p q hqj hqodd'
    have hsign : (-1 : ℝ) ^ (d + q.card) = -((-1 : ℝ) ^ d) := by
      rw [pow_add]
      have hpow : (-1 : ℝ) ^ q.card = -1 := by
        rcases hqodd' with ⟨m, hm⟩
        rw [hm]
        norm_num [pow_add]
      rw [hpow]
      ring
    refine ⟨B, A, ?_, ?_, ?_, ?_, ?_, hBdeg, hAdeg⟩
    · simpa [add_comm] using hsum
    · intro x
      exact (hpar x).2
    · intro x
      exact (hpar x).1
    · simpa [hsign] using hB'
    · rw [hsign] at hA'
      simpa using hA'

/-! ## A compiled local orbit reorientation

For a star-separated orbit of odd cardinality, the two opposite
orientations have opposite reflected root-product coefficient.  The lemma
is deliberately stated at the multiset level, so multiplicities in a later
sum of orbit chunks remain visible. -/

lemma reflectCoeff_add023 (s t : Multiset ℂ) :
    reflectCoeff022 (s + t) =
      reflectCoeff022 s * reflectCoeff022 t := by
  simp only [reflectCoeff022, nonzeroProduct022,
    Multiset.filter_add, Multiset.card_add,
    Multiset.prod_add, pow_add]
  ring

lemma orbitFin020_ne_zero_of_disjoint023
    (a : ℂ) (hdisj : Disjoint (orbitFin020 a) (orbitStarFin020 a)) :
    ∀ z ∈ (orbitFin020 a).1, z ≠ 0 := by
  intro z hzK hz0
  have hzL : (starRingEnd ℂ) z ∈ orbitStarFin020 a := by
    rw [orbitStarFin020]
    exact Finset.mem_map.mpr ⟨z, hzK, rfl⟩
  have hzL0 : (0 : ℂ) ∈ orbitStarFin020 a := by
    simpa [hz0] using hzL
  subst z
  exact (Finset.disjoint_left.mp hdisj hzK hzL0)

theorem orientation_replace_chunk023
    (s q r K L : Multiset ℂ)
    (hpart : s = q + Multiset.map (starRingEnd ℂ) q)
    (hq : q = K + r)
    (hKstar : Multiset.map (starRingEnd ℂ) K = L)
    (hLstar : Multiset.map (starRingEnd ℂ) L = K)
    (hLj : Multiset.map starNegMap020 L = L)
    (hLi : Multiset.map invStar127 L = L)
    (hrj : Multiset.map starNegMap020 r = r)
    (hri : Multiset.map invStar127 r = r)
    (hflip : reflectCoeff022 K = -reflectCoeff022 L) :
    ∃ q' : Multiset ℂ,
      s = q' + Multiset.map (starRingEnd ℂ) q' ∧
      Multiset.map starNegMap020 q' = q' ∧
      Multiset.map invStar127 q' = q' ∧
      reflectCoeff022 q' = -reflectCoeff022 q := by
  refine ⟨L + r, ?_, ?_, ?_, ?_⟩
  · calc
      s = q + Multiset.map (starRingEnd ℂ) q := hpart
      _ = (K + r) + Multiset.map (starRingEnd ℂ) (K + r) := by
        rw [hq]
      _ = (L + r) + Multiset.map (starRingEnd ℂ) (L + r) := by
        simp only [Multiset.map_add]
        rw [hKstar, hLstar]
        ac_rfl
  · rw [Multiset.map_add, hLj, hrj]
  · rw [Multiset.map_add, hLi, hri]
  · rw [reflectCoeff_add023, hq, reflectCoeff_add023, hflip]
    ring

lemma real_unit_eq_target_or_neg023
    (c t : ℂ)
    (hcreal : (starRingEnd ℂ) c = c)
    (hc : Complex.normSq c = 1)
    (htreal : (starRingEnd ℂ) t = t)
    (ht : Complex.normSq t = 1) :
    c = t ∨ c = -t := by
  have hcc : c * c = 1 := by
    have h := Complex.mul_conj c
    rw [hcreal, hc] at h
    simpa using h
  have htt : t * t = 1 := by
    have h := Complex.mul_conj t
    rw [htreal, ht] at h
    simpa using h
  by_cases hct : c = t
  · exact Or.inl hct
  · have hzero : (c - t) * (c + t) = 0 := by
      calc
        (c - t) * (c + t) = c * c - t * t := by ring
        _ = 0 := by rw [hcc, htt]; ring
    rcases mul_eq_zero.mp hzero with hleft | hright
    · exact (hct (sub_eq_zero.mp hleft)).elim
    · right
      calc
        c = (c + t) - t := by ring
        _ = -t := by rw [hright]; ring

theorem select_reflect_target_from_pair023
    (s : Multiset ℂ) (d : ℕ)
    (q₁ q₂ : Multiset ℂ)
    (hwidth₁ : q₁.card + q₁.count 0 = 2 * d)
    (hwidth₂ : q₂.card + q₂.count 0 = 2 * d)
    (hpart₁ : s = q₁ + Multiset.map (starRingEnd ℂ) q₁)
    (hpart₂ : s = q₂ + Multiset.map (starRingEnd ℂ) q₂)
    (hq₁j : Multiset.map starNegMap020 q₁ = q₁)
    (hq₁i : Multiset.map invStar127 q₁ = q₁)
    (hq₂j : Multiset.map starNegMap020 q₂ = q₂)
    (hq₂i : Multiset.map invStar127 q₂ = q₂)
    (hflip : reflectCoeff022 q₁ = -reflectCoeff022 q₂) :
    ∃ q : Multiset ℂ,
      s = q + Multiset.map (starRingEnd ℂ) q ∧
      Multiset.map starNegMap020 q = q ∧
      Multiset.map invStar127 q = q ∧
      q.card + q.count 0 = 2 * d ∧
      reflectCoeff022 q = (-1 : ℂ) ^ (d + q.card) := by
  have hcard₁ := congrArg Multiset.card hpart₁
  have hcard₂ := congrArg Multiset.card hpart₂
  have hcard : q₁.card = q₂.card := by
    simp only [Multiset.card_add, Multiset.card_map] at hcard₁ hcard₂
    omega
  let t : ℂ := (-1 : ℂ) ^ (d + q₁.card)
  have ht : Complex.normSq t = 1 := by
    dsimp [t]
    induction d + q₁.card with
    | zero => norm_num
    | succ n ih =>
        rw [pow_succ, Complex.normSq_mul, ih]
        norm_num
  have htreal : (starRingEnd ℂ) t = t := by
    dsimp [t]
    exact unit_sign_real022 (d + q₁.card)
  have hc₁ : Complex.normSq (reflectCoeff022 q₁) = 1 :=
    reflectCoeff_unit022 q₁ hq₁i
  have hcreal₁ : (starRingEnd ℂ) (reflectCoeff022 q₁) =
      reflectCoeff022 q₁ :=
    reflectCoeff_real022 q₁ d hq₁j hwidth₁
  have hcases := real_unit_eq_target_or_neg023
    (reflectCoeff022 q₁) t hcreal₁ hc₁ htreal ht
  rcases hcases with hgood | hbad
  · refine ⟨q₁, hpart₁, hq₁j, hq₁i, hwidth₁, ?_⟩
    exact hgood
  · have hq₂target : reflectCoeff022 q₂ = t := by
      exact neg_injective127 (hflip.symm.trans hbad)
    refine ⟨q₂, hpart₂, hq₂j, hq₂i, hwidth₂, ?_⟩
    calc
      reflectCoeff022 q₂ = t := hq₂target
      _ = (-1 : ℂ) ^ (d + q₂.card) := by
        dsimp [t]
        rw [hcard]

theorem orient_from_odd_chunk023
    (s q r K L : Multiset ℂ) (d : ℕ)
    (hpart : s = q + Multiset.map (starRingEnd ℂ) q)
    (hqj : Multiset.map starNegMap020 q = q)
    (hqi : Multiset.map invStar127 q = q)
    (hq : q = K + r)
    (hKstar : Multiset.map (starRingEnd ℂ) K = L)
    (hLstar : Multiset.map (starRingEnd ℂ) L = K)
    (hLj : Multiset.map starNegMap020 L = L)
    (hLi : Multiset.map invStar127 L = L)
    (hrj : Multiset.map starNegMap020 r = r)
    (hri : Multiset.map invStar127 r = r)
    (hflip : reflectCoeff022 K = -reflectCoeff022 L)
    (hwidth : q.card + q.count 0 = 2 * d) :
    ∃ q' : Multiset ℂ,
      s = q' + Multiset.map (starRingEnd ℂ) q' ∧
      Multiset.map starNegMap020 q' = q' ∧
      Multiset.map invStar127 q' = q' ∧
      q'.card + q'.count 0 = 2 * d ∧
      reflectCoeff022 q' = (-1 : ℂ) ^ (d + q'.card) := by
  obtain ⟨qalt, hpart_alt, hqaltj, hqalti, hcoeff_alt⟩ :=
    orientation_replace_chunk023 s q r K L hpart hq hKstar hLstar
      hLj hLi hrj hri hflip
  have hcard_qalt : q.card = qalt.card := by
    have hc₁ := congrArg Multiset.card hpart
    have hc₂ := congrArg Multiset.card hpart_alt
    simp only [Multiset.card_add, Multiset.card_map] at hc₁ hc₂
    omega
  have hzero_qalt : q.count 0 = qalt.count 0 := by
    have hz₁ := congrArg (fun m : Multiset ℂ => m.count 0) hpart
    have hz₂ := congrArg (fun m : Multiset ℂ => m.count 0) hpart_alt
    simp only [Multiset.count_add] at hz₁ hz₂
    rw [count_star_zero021] at hz₁
    rw [count_star_zero021] at hz₂
    omega
  have hwidth_alt' : qalt.card + qalt.count 0 = 2 * d := by
    omega
  have hflip' : reflectCoeff022 q = -reflectCoeff022 qalt := by
    rw [hcoeff_alt]
    ring
  exact select_reflect_target_from_pair023 s d q qalt hwidth hwidth_alt'
    hpart hpart_alt
    hqj hqi
    hqaltj hqalti
    hflip'

/-! ## The qBad regression and its orbit-reselected positive -/

/-! A nonzero point fixed by the two different involution descriptions cannot
    identify their images.  This small algebraic fact is used to keep the
    four-point orbit decomposition multiplicity-exact. -/

lemma starNeg_eq_invStar_implies_fixed023
    (a : ℂ) (ha : a ≠ 0)
    (h : starNegMap020 a = invStar127 a) :
    starNegMap020 a = a := by
  have h' : -(starRingEnd ℂ) a = ((starRingEnd ℂ) a)⁻¹ := by
    simpa [starNegMap020, invStar127] using h
  have hsa : (starRingEnd ℂ) a ≠ 0 := by
    intro hzero
    apply ha
    have hzero' := congrArg (starRingEnd ℂ) hzero
    simpa using hzero'
  have hmul : (starRingEnd ℂ) a * (starRingEnd ℂ) a = -1 := by
    calc
      (starRingEnd ℂ) a * (starRingEnd ℂ) a =
          -((-(starRingEnd ℂ) a) * (starRingEnd ℂ) a) := by ring
      _ = -(((starRingEnd ℂ) a)⁻¹ * (starRingEnd ℂ) a) := by rw [h']
      _ = -1 := by rw [inv_mul_cancel₀ hsa]
  have hsq : a * a = -1 := by
    have hs := congrArg (starRingEnd ℂ) hmul
    simpa [map_mul] using hs
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp [Complex.mul_re, Complex.mul_im] at hre him
  have hxy : a.re * a.im = 0 := by linarith
  rcases mul_eq_zero.mp hxy with hx | hy
  · apply Complex.ext
    · change -a.re = a.re
      linarith
    · simp [starNegMap020]
  · have hsqre : 0 ≤ a.re * a.re := by
      simpa [pow_two] using (sq_nonneg a.re)
    rw [hy] at hre
    nlinarith [hsqre]

lemma orbit_four_prod_value023
    (a : ℂ) (ha : a ≠ 0)
    (hj : starNegMap020 a ≠ a)
    (hi : invStar127 a ≠ a) :
    ((orbitFin020 a).1).prod = 1 := by
  have hji : starNegMap020 a ≠ invStar127 a := by
    intro h
    exact hj (starNeg_eq_invStar_implies_fixed023 a ha h)
  have hia : a ≠ invStar127 a := Ne.symm hi
  have hja : a ≠ starNegMap020 a := Ne.symm hj
  have hjad : starNegMap020 a ≠
      starNegMap020 (invStar127 a) := by
    intro h
    apply hi
    exact (starNegMap020_injective h).symm
  have hidi : invStar127 a ≠
      starNegMap020 (invStar127 a) := by
    intro h
    apply hj
    have hiaeq : invStar127 (starNegMap020 a) = invStar127 a := by
      calc
        invStar127 (starNegMap020 a) =
            starNegMap020 (invStar127 a) :=
          (starNegMap020_invStar_comm a).symm
        _ = invStar127 a := h.symm
    exact invStar127_injective hiaeq
  have hadi : a ≠ starNegMap020 (invStar127 a) := by
    intro h
    have hji' : starNegMap020 a = invStar127 a := by
      have hh := congrArg starNegMap020 h
      calc
        starNegMap020 a =
            starNegMap020 (starNegMap020 (invStar127 a)) := hh
        _ = invStar127 a := starNegMap020_involutive _
    exact hji hji'
  have hset : orbitFin020 a =
      {a, starNegMap020 a, invStar127 a,
        starNegMap020 (invStar127 a)} := by rfl
  rw [hset]
  have h0 : a ∉ ({starNegMap020 a, invStar127 a,
      starNegMap020 (invStar127 a)} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [Finset.insert_val_of_notMem h0]
  have h1 : starNegMap020 a ∉
      ({invStar127 a, starNegMap020 (invStar127 a)} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [Finset.insert_val_of_notMem h1]
  have h2 : invStar127 a ∉
      ({starNegMap020 (invStar127 a)} : Finset ℂ) := by
    simp only [Finset.mem_singleton]
    exact hidi
  rw [Finset.insert_val_of_notMem h2]
  simp only [Finset.singleton_val, Multiset.prod_cons,
    Multiset.prod_singleton]
  simp only [starNegMap020, invStar127]
  field_simp [ha]
  have hstarinv :
      (starRingEnd ℂ) (1 / (starRingEnd ℂ) a) = a⁻¹ := by
    simp
  rw [hstarinv]
  exact mul_inv_cancel₀ ha

lemma orbit_two_j_fixed023
    (a : ℂ)
    (hj : starNegMap020 a = a)
    (_hi : invStar127 a ≠ a) :
    orbitFin020 a = {a, invStar127 a} := by
  have hij : starNegMap020 (invStar127 a) = invStar127 a := by
    calc
      starNegMap020 (invStar127 a) = invStar127 (starNegMap020 a) :=
        starNegMap020_invStar_comm a
      _ = invStar127 a := by rw [hj]
  apply Finset.ext
  intro z
  simp only [orbitFin020, Finset.mem_insert, Finset.mem_singleton]
  rw [hj, hij]
  tauto

lemma orbit_two_i_fixed023
    (a : ℂ)
    (_hj : starNegMap020 a ≠ a)
    (hi : invStar127 a = a) :
    orbitFin020 a = {a, starNegMap020 a} := by
  apply Finset.ext
  intro z
  simp only [orbitFin020, Finset.mem_insert, Finset.mem_singleton]
  rw [hi]
  tauto

lemma orbit_two_j_fixed_prod_value023
    (a : ℂ) (ha : a ≠ 0)
    (hj : starNegMap020 a = a)
    (hi : invStar127 a ≠ a) :
    ((orbitFin020 a).1).prod = -1 := by
  have hij : starNegMap020 (invStar127 a) = invStar127 a := by
    calc
      starNegMap020 (invStar127 a) = invStar127 (starNegMap020 a) :=
        starNegMap020_invStar_comm a
      _ = invStar127 a := by rw [hj]
  have horbit : orbitFin020 a = {a, invStar127 a} := by
    apply Finset.ext
    intro z
    simp only [orbitFin020, Finset.mem_insert, Finset.mem_singleton]
    rw [hj, hij]
    tauto
  rw [horbit]
  have hnot : a ∉ ({invStar127 a} : Finset ℂ) := by
    simp [Ne.symm hi]
  rw [Finset.insert_val_of_notMem hnot]
  simp
  rw [show invStar127 a = ((starRingEnd ℂ) a)⁻¹ by rfl]
  have hj' : (starRingEnd ℂ) a = -a := by
    calc
      (starRingEnd ℂ) a = -(-(starRingEnd ℂ) a) := by ring
      _ = -a := by rw [show -(starRingEnd ℂ) a = a by
        simpa [starNegMap020] using hj]
  rw [hj']
  field_simp

lemma orbit_two_i_fixed_prod_value023
    (a : ℂ) (ha : a ≠ 0)
    (hj : starNegMap020 a ≠ a)
    (hi : invStar127 a = a) :
    ((orbitFin020 a).1).prod = -1 := by
  have horbit : orbitFin020 a = {a, starNegMap020 a} := by
    apply Finset.ext
    intro z
    simp only [orbitFin020, Finset.mem_insert, Finset.mem_singleton]
    rw [hi]
    tauto
  rw [horbit]
  have hnot : a ∉ ({starNegMap020 a} : Finset ℂ) := by
    intro h
    apply Ne.symm hj
    simpa using h
  rw [Finset.insert_val_of_notMem hnot]
  rw [Multiset.prod_cons]
  have hsingleton :
      ({starNegMap020 a} : Finset ℂ).1 =
        starNegMap020 a ::ₘ (0 : Multiset ℂ) := by
    rw [Finset.singleton_val]
    simp
  rw [hsingleton, Multiset.prod_cons]
  simp only [Multiset.prod_zero, mul_one]
  have hi' : (starRingEnd ℂ) a = a⁻¹ := by
    have h := congrArg (starRingEnd ℂ) hi
    simpa [invStar127] using h.symm
  simp only [starNegMap020]
  rw [hi']
  field_simp

lemma orbit_even_reflectCoeff023
    (a : ℂ) (ha : a ≠ 0)
    (hcard : Even (orbitFin020 a).card) :
    reflectCoeff022 (orbitFin020 a).1 =
      (-1 : ℂ) ^ ((orbitFin020 a).card / 2) := by
  have hstar_ne : (starRingEnd ℂ) a ≠ 0 := by
    intro hzero
    apply ha
    have hzero' := congrArg (starRingEnd ℂ) hzero
    simpa using hzero'
  have hi_ne : invStar127 a ≠ 0 := by
    simp [invStar127, hstar_ne]
  have hj_ne : starNegMap020 a ≠ 0 := by
    simp [starNegMap020, hstar_ne]
  have hji_ne : starNegMap020 (invStar127 a) ≠ 0 := by
    have hstar_i_ne : (starRingEnd ℂ) (invStar127 a) ≠ 0 := by
      intro hzero
      have hzero' := congrArg (starRingEnd ℂ) hzero
      apply hi_ne
      simpa using hzero'
    simp [starNegMap020, hstar_i_ne]
  have hKne : ∀ z ∈ (orbitFin020 a).1, z ≠ 0 := by
    intro z hz
    have hz' : z ∈ orbitFin020 a := by simpa using hz
    simp only [orbitFin020, Finset.mem_insert, Finset.mem_singleton] at hz'
    rcases hz' with rfl | rfl | rfl | rfl
    · exact ha
    · exact hj_ne
    · exact hi_ne
    · exact hji_ne
  have hfilter : ((orbitFin020 a).1).filter
      (fun z : ℂ => z ≠ 0) = (orbitFin020 a).1 :=
    Multiset.filter_eq_self.mpr hKne
  have hcoeff : reflectCoeff022 (orbitFin020 a).1 =
      (-1 : ℂ) ^ (orbitFin020 a).card *
        ((orbitFin020 a).1).prod := by
    simp [reflectCoeff022, nonzeroProduct022, hfilter]
  by_cases hjfix : starNegMap020 a = a
  · by_cases hifix : invStar127 a = a
    · have hij : starNegMap020 (invStar127 a) = invStar127 a := by
        calc
          starNegMap020 (invStar127 a) =
              invStar127 (starNegMap020 a) :=
            starNegMap020_invStar_comm a
          _ = invStar127 a := by rw [hjfix]
      have horbit : orbitFin020 a = ({a} : Finset ℂ) := by
        apply Finset.ext
        intro z
        have hja : starNegMap020 a = a := hjfix
        have hja' : -(starRingEnd ℂ) a = a := by
          simpa [starNegMap020] using hja
        simp only [orbitFin020, Finset.mem_insert, Finset.mem_singleton]
        simp [hja', hifix]
      have hcard_one : (orbitFin020 a).card = 1 := by
        rw [horbit]
        simp
      have hnot_even : ¬ Even (orbitFin020 a).card := by
        rw [hcard_one]
        norm_num
      exact (hnot_even hcard).elim
    · have hprod := orbit_two_j_fixed_prod_value023 a ha hjfix hifix
      have horbit := orbit_two_j_fixed023 a hjfix hifix
      have hnot : a ∉ ({invStar127 a} : Finset ℂ) := by
        simp [Ne.symm hifix]
      have hcard_two : (orbitFin020 a).card = 2 := by
        rw [horbit, Finset.card_insert_of_notMem hnot]
        simp
      rw [hcoeff, hprod, hcard_two]
      norm_num
  · by_cases hifix : invStar127 a = a
    · have hprod := orbit_two_i_fixed_prod_value023 a ha hjfix hifix
      have horbit := orbit_two_i_fixed023 a hjfix hifix
      have hnot : a ∉ ({starNegMap020 a} : Finset ℂ) := by
        intro h
        apply Ne.symm hjfix
        simpa using h
      have hcard_two : (orbitFin020 a).card = 2 := by
        rw [horbit, Finset.card_insert_of_notMem hnot]
        simp
      rw [hcoeff, hprod, hcard_two]
      norm_num
    · have hprod := orbit_four_prod_value023 a ha hjfix hifix
      have hji : starNegMap020 a ≠ invStar127 a := by
        intro h
        exact hjfix (starNeg_eq_invStar_implies_fixed023 a ha h)
      have hia : a ≠ invStar127 a := Ne.symm hifix
      have hja : a ≠ starNegMap020 a := Ne.symm hjfix
      have hjad : starNegMap020 a ≠
          starNegMap020 (invStar127 a) := by
        intro h
        apply hifix
        exact (starNegMap020_injective h).symm
      have hidi : invStar127 a ≠
          starNegMap020 (invStar127 a) := by
        intro h
        apply hjfix
        have hiaeq : invStar127 (starNegMap020 a) =
            invStar127 a := by
          calc
            invStar127 (starNegMap020 a) =
                starNegMap020 (invStar127 a) :=
              (starNegMap020_invStar_comm a).symm
            _ = invStar127 a := h.symm
        exact invStar127_injective hiaeq
      have hadi : a ≠ starNegMap020 (invStar127 a) := by
        intro h
        have hji' : starNegMap020 a = invStar127 a := by
          have hh := congrArg starNegMap020 h
          calc
            starNegMap020 a =
                starNegMap020 (starNegMap020 (invStar127 a)) := hh
            _ = invStar127 a := starNegMap020_involutive _
        exact hji hji'
      have hset : orbitFin020 a =
          {a, starNegMap020 a, invStar127 a,
            starNegMap020 (invStar127 a)} := by rfl
      have h0 : a ∉ ({starNegMap020 a, invStar127 a,
          starNegMap020 (invStar127 a)} : Finset ℂ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      have h1 : starNegMap020 a ∉
          ({invStar127 a, starNegMap020 (invStar127 a)} : Finset ℂ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      have h2 : invStar127 a ∉
          ({starNegMap020 (invStar127 a)} : Finset ℂ) := by
        simp only [Finset.mem_singleton]
        exact hidi
      have hcard_four : (orbitFin020 a).card = 4 := by
        rw [hset]
        rw [Finset.card_insert_of_notMem h0]
        rw [Finset.card_insert_of_notMem h1]
        rw [Finset.card_insert_of_notMem h2]
        simp
      rw [hcoeff, hprod, hcard_four]
      norm_num

lemma orbit_orientation_flip_coeff023
    (a : ℂ) (hdisj : Disjoint (orbitFin020 a) (orbitStarFin020 a))
    (hodd : Odd (orbitFin020 a).card) :
    reflectCoeff022 (orbitFin020 a).1 =
      -reflectCoeff022 (orbitStarFin020 a).1 := by
  let K : Multiset ℂ := (orbitFin020 a).1
  let L : Multiset ℂ := (orbitStarFin020 a).1
  have hKstar : Multiset.map (starRingEnd ℂ) K = L := by
    simpa [K, L] using (orbitStarFin020_val a).symm
  have hLstar : Multiset.map (starRingEnd ℂ) L = K := by
    rw [← hKstar]
    rw [Multiset.map_map]
    induction K using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
        simp only [Multiset.map_cons, Function.comp_apply]
        rw [star_involutive127]
        congr 1
  have hKj : Multiset.map starNegMap020 K = K := by
    simpa [K] using orbitFin020_map_starNeg a
  have hKne : ∀ z ∈ K, z ≠ 0 := by
    intro z hz
    exact orbitFin020_ne_zero_of_disjoint023 a hdisj z (by simpa [K] using hz)
  have hLne : ∀ z ∈ L, z ≠ 0 := by
    intro z hz
    have hzK : (starRingEnd ℂ) z ∈ K := by
      rw [← hLstar]
      exact Multiset.mem_map_of_mem (starRingEnd ℂ) hz
    intro hz0
    have hstarzero : (starRingEnd ℂ) z = 0 := by
      rw [hz0]
      simp
    exact (hKne ((starRingEnd ℂ) z) hzK) hstarzero
  have hKfilter : K.filter (fun z : ℂ => z ≠ 0) = K :=
    Multiset.filter_eq_self.mpr hKne
  have hLfilter : L.filter (fun z : ℂ => z ≠ 0) = L :=
    Multiset.filter_eq_self.mpr hLne
  have hcard : L.card = K.card := by
    have hcard' := congrArg Multiset.card hKstar
    calc
      L.card = (Multiset.map (starRingEnd ℂ) K).card := hcard'.symm
      _ = K.card := by simp
  have hprodK : K.prod =
      (-1 : ℂ) ^ K.card * (starRingEnd ℂ) K.prod := by
    calc
      K.prod = (Multiset.map starNegMap020 K).prod := by rw [hKj]
      _ = (-1 : ℂ) ^ K.card * (starRingEnd ℂ) K.prod :=
        prod_map_starNeg022 K
  have hoddK : Odd K.card := by simpa [K] using hodd
  have hoddPow : (-1 : ℂ) ^ K.card = -1 := by
    rcases hoddK with ⟨m, hm⟩
    rw [hm]
    norm_num [pow_add]
  have hstarProd : (starRingEnd ℂ) K.prod = -K.prod := by
    have hprodK' : K.prod = -(starRingEnd ℂ) K.prod := by
      simpa [hoddPow] using hprodK
    calc
      (starRingEnd ℂ) K.prod = -(-(starRingEnd ℂ) K.prod) := by ring
      _ = -K.prod := by rw [← hprodK']
  have hprodL : L.prod = (starRingEnd ℂ) K.prod := by
    calc
      L.prod = (Multiset.map (starRingEnd ℂ) K).prod := by rw [hKstar]
      _ = (starRingEnd ℂ) K.prod := by
        induction K using Multiset.induction_on with
        | empty => simp
        | cons a s ih =>
            simp only [Multiset.map_cons, Multiset.prod_cons]
            rw [ih]
            exact (map_mul (starRingEnd ℂ) a s.prod).symm
  have hcoeffK : reflectCoeff022 K =
      (-1 : ℂ) ^ K.card * K.prod := by
    simp [reflectCoeff022, nonzeroProduct022, hKfilter]
  have hcoeffL : reflectCoeff022 L =
      (-1 : ℂ) ^ L.card * L.prod := by
    simp [reflectCoeff022, nonzeroProduct022, hLfilter]
  rw [hcoeffK, hcoeffL, hcard, hoddPow, hprodL, hstarProd]
  ring

lemma orbit_overlap_even023
    (a : ℂ) (ha : a ≠ 0)
    (hoverlap : (starRingEnd ℂ) a ∈ orbitFin020 a) :
    Even (orbitFin020 a).card := by
  have hstarfix : ∀ z ∈ orbitFin020 a,
      (starRingEnd ℂ) z = z :=
    star_fixed_on_orbit_of_overlap020 a hoverlap
  have haK : a ∈ orbitFin020 a := by simp [orbitFin020]
  have hja : starNegMap020 a ≠ a := by
    intro hj
    have hsa : (starRingEnd ℂ) a = a := hstarfix a haK
    have hneg : -a = a := by
      calc
        -a = -(starRingEnd ℂ) a := by rw [hsa]
        _ = a := by simpa [starNegMap020] using hj
    have ha0 : a = 0 := by
      have hsum := congrArg (fun z : ℂ => z + a) hneg
      have htwice : (2 : ℂ) * a = 0 := by
        calc
          (2 : ℂ) * a = a + a := by ring
          _ = 0 := by simpa using hsum.symm
      rcases mul_eq_zero.mp htwice with htwo | ha0
      · norm_num at htwo
      · exact ha0
    exact ha ha0
  by_cases hi : invStar127 a = a
  · have horbit := orbit_two_i_fixed023 a hja hi
    have hnot : a ∉ ({starNegMap020 a} : Finset ℂ) := by
      intro h
      apply Ne.symm hja
      simpa using h
    rw [horbit]
    rw [Finset.card_insert_of_notMem hnot]
    simp
  · by_cases hj : starNegMap020 a = a
    · exact (hja hj).elim
    · have hji : starNegMap020 a ≠ invStar127 a := by
        intro h
        exact hj (starNeg_eq_invStar_implies_fixed023 a ha h)
      have hia : a ≠ invStar127 a := Ne.symm hi
      have hja' : a ≠ starNegMap020 a := Ne.symm hj
      have hjad : starNegMap020 a ≠
          starNegMap020 (invStar127 a) := by
        intro h
        apply hi
        exact (starNegMap020_injective h).symm
      have hidi : invStar127 a ≠
          starNegMap020 (invStar127 a) := by
        intro h
        apply hj
        have hiaeq : invStar127 (starNegMap020 a) =
            invStar127 a := by
          calc
            invStar127 (starNegMap020 a) =
                starNegMap020 (invStar127 a) :=
              (starNegMap020_invStar_comm a).symm
            _ = invStar127 a := h.symm
        exact invStar127_injective hiaeq
      have hadi : a ≠ starNegMap020 (invStar127 a) := by
        intro h
        have hji' : starNegMap020 a = invStar127 a := by
          have hh := congrArg starNegMap020 h
          calc
            starNegMap020 a =
                starNegMap020 (starNegMap020 (invStar127 a)) := hh
            _ = invStar127 a := starNegMap020_involutive _
        exact hji hji'
      have hset : orbitFin020 a =
          {a, starNegMap020 a, invStar127 a,
            starNegMap020 (invStar127 a)} := by rfl
      have h0 : a ∉ ({starNegMap020 a, invStar127 a,
          starNegMap020 (invStar127 a)} : Finset ℂ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      have h1 : starNegMap020 a ∉
          ({invStar127 a, starNegMap020 (invStar127 a)} : Finset ℂ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      have h2 : invStar127 a ∉
          ({starNegMap020 (invStar127 a)} : Finset ℂ) := by
        simp only [Finset.mem_singleton]
        exact hidi
      rw [hset]
      rw [Finset.card_insert_of_notMem h0]
      rw [Finset.card_insert_of_notMem h1]
      rw [Finset.card_insert_of_notMem h2]
      norm_num

lemma orbitFin020_ne_zero_of_ne_zero023
    (a : ℂ) (ha : a ≠ 0) :
    ∀ z ∈ (orbitFin020 a).1, z ≠ 0 := by
  have hstar_ne : (starRingEnd ℂ) a ≠ 0 := by
    intro hzero
    apply ha
    have hzero' := congrArg (starRingEnd ℂ) hzero
    simpa using hzero'
  have hi_ne : invStar127 a ≠ 0 := by
    simp [invStar127, hstar_ne]
  have hj_ne : starNegMap020 a ≠ 0 := by
    simp [starNegMap020, hstar_ne]
  have hji_ne : starNegMap020 (invStar127 a) ≠ 0 := by
    have hstar_i_ne : (starRingEnd ℂ) (invStar127 a) ≠ 0 := by
      intro hzero
      have hzero' := congrArg (starRingEnd ℂ) hzero
      apply hi_ne
      simpa using hzero'
    simp [starNegMap020, hstar_i_ne]
  intro z hz
  have hz' : z ∈ orbitFin020 a := by simpa using hz
  simp only [orbitFin020, Finset.mem_insert, Finset.mem_singleton] at hz'
  rcases hz' with rfl | rfl | rfl | rfl
  · exact ha
  · exact hj_ne
  · exact hi_ne
  · exact hji_ne

lemma neg_one_pow_add_two023 (n : ℕ) :
    (-1 : ℂ) ^ (n + 2) = (-1 : ℂ) ^ n := by
  rw [pow_add]
  norm_num

lemma neg_one_pow_even023 (n : ℕ) :
    (-1 : ℂ) ^ (n + n) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show n + 1 + (n + 1) = (n + n) + 2 by omega,
        pow_add]
      rw [neg_one_pow_add_two023]
      rw [pow_zero, mul_one]
      exact ih

lemma width_sub_double023 (A m e : ℕ)
    (h : 2 * m + A = 2 * e) (hme : m ≤ e) :
    A = 2 * (e - m) := by
  have hsub : e - m + m = e := Nat.sub_add_cancel hme
  have hdouble : 2 * (e - m) + 2 * m = 2 * e := by
    calc
      2 * (e - m) + 2 * m = 2 * ((e - m) + m) := by ring
      _ = 2 * e := by rw [hsub]
  have hsum : A + 2 * m = 2 * (e - m) + 2 * m := by
    calc
      A + 2 * m = 2 * m + A := by ac_rfl
      _ = 2 * e := h
      _ = 2 * (e - m) + 2 * m := hdouble.symm
  exact Nat.add_right_cancel hsum

theorem orient_half_target023
    (q : Multiset ℂ) (d : ℕ)
    (hqj : Multiset.map starNegMap020 q = q)
    (hqi : Multiset.map invStar127 q = q)
    (hwidth : q.card + q.count 0 = 2 * d) :
    ∃ q' : Multiset ℂ,
      q + Multiset.map (starRingEnd ℂ) q =
          q' + Multiset.map (starRingEnd ℂ) q' ∧
      Multiset.map starNegMap020 q' = q' ∧
      Multiset.map invStar127 q' = q' ∧
      q'.card + q'.count 0 = 2 * d ∧
      reflectCoeff022 q' = (-1 : ℂ) ^ (d + q'.card) := by
  have hP : ∀ n : ℕ, ∀ t : Multiset ℂ, ∀ e : ℕ,
      t.card = n →
      Multiset.map starNegMap020 t = t →
      Multiset.map invStar127 t = t →
      t.card + t.count 0 = 2 * e →
      ∃ u : Multiset ℂ,
        t + Multiset.map (starRingEnd ℂ) t =
            u + Multiset.map (starRingEnd ℂ) u ∧
        Multiset.map starNegMap020 u = u ∧
        Multiset.map invStar127 u = u ∧
        u.card + u.count 0 = 2 * e ∧
        reflectCoeff022 u = (-1 : ℂ) ^ (e + u.card) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro t e ht htj hti htwidth
        by_cases ht0 : t = 0
        · subst t
          simp at htwidth
          have he : e = 0 := htwidth
          refine ⟨0, by simp, by simp, by simp, by simp [he], ?_⟩
          simp [he, reflectCoeff022, nonzeroProduct022]
        · obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero ht0
          let K : Finset ℂ := orbitFin020 a
          let L : Finset ℂ := orbitStarFin020 a
          have hKmem : ∀ z ∈ K, z ∈ t := by
            intro z hz
            simpa [K] using orbitFin020_mem_of_mem t a ha htj hti hz
          have hKle : (K.1 : Multiset ℂ) ≤ t :=
            finset_val_le_of_mem020 t K hKmem
          have hKj : Multiset.map starNegMap020 K.1 = K.1 := by
            simpa [K] using orbitFin020_map_starNeg a
          have hKi : Multiset.map invStar127 K.1 = K.1 := by
            simpa [K] using orbitFin020_map_invStar a
          have hLval : L.1 =
              Multiset.map (starRingEnd ℂ) K.1 := by
            simpa [K, L] using orbitStarFin020_val a
          have hKstar : Multiset.map (starRingEnd ℂ) K.1 = L.1 :=
            hLval.symm
          have hLstar : Multiset.map (starRingEnd ℂ) L.1 = K.1 := by
            rw [← hKstar]
            rw [Multiset.map_map]
            induction K.1 using Multiset.induction_on with
            | empty => simp
            | cons b s ihs =>
                simp only [Multiset.map_cons, Function.comp_apply]
                rw [star_involutive127]
                congr 1
          have hLj : Multiset.map starNegMap020 L.1 = L.1 := by
            rw [← hKstar]
            rw [Multiset.map_map]
            rw [show (starNegMap020 ∘ (starRingEnd ℂ)) =
                (starRingEnd ℂ) ∘ starNegMap020 by
                  funext z
                  exact starNegMap020_star_comm z]
            rw [← Multiset.map_map, hKj]
          have hLi : Multiset.map invStar127 L.1 = L.1 := by
            rw [← hKstar]
            rw [Multiset.map_map]
            rw [show (invStar127 ∘ (starRingEnd ℂ)) =
                (starRingEnd ℂ) ∘ invStar127 by
                  funext z
                  simp [invStar127]]
            rw [← Multiset.map_map, hKi]
          let r : Multiset ℂ := t - K.1
          have hdec : t = K.1 + r := by
            dsimp [r]
            exact residual_decomposition020 t K.1 hKle
          have hlt : r < t := by
            dsimp [r]
            exact residual_lt020 t K.1 hKle (by
              intro hz
              have haz : a ∈ K.1 := by simp [K, orbitFin020]
              rw [hz] at haz
              simp at haz)
          have hrcard : r.card < n := by
            have hc : r.card < t.card := Multiset.card_lt_card hlt
            exact hc.trans_eq ht
          have hrj : Multiset.map starNegMap020 r = r := by
            dsimp [r]
            exact residual_invariant020 t K.1 hKle
              starNegMap020 htj hKj
          have hri : Multiset.map invStar127 r = r := by
            dsimp [r]
            exact residual_invariant020 t K.1 hKle
              invStar127 hti hKi
          by_cases hdisj : Disjoint K L
          · have ha0 : a ≠ 0 := by
              exact orbitFin020_ne_zero_of_disjoint023 a
                (by simpa [K, L] using hdisj) a (by simp [orbitFin020])
            by_cases hodd : Odd K.card
            · have hoddK : Odd (orbitFin020 a).card := by
                simpa [K] using hodd
              have hflip : reflectCoeff022 K.1 =
                  -reflectCoeff022 L.1 :=
                orbit_orientation_flip_coeff023 a
                  (by simpa [K, L] using hdisj) hoddK
              obtain ⟨u, husum, huj, hui, huw, huc⟩ :=
                orient_from_odd_chunk023
                  (t + Multiset.map (starRingEnd ℂ) t) t r K.1 L.1 e
                  rfl htj hti hdec hKstar hLstar hLj hLi hrj hri hflip
                  htwidth
              exact ⟨u, husum, huj, hui, huw, huc⟩
            · have heven : Even K.card := by
                rcases Nat.even_or_odd K.card with he | ho
                · exact he
                · exact (hodd ho).elim
              rcases heven with ⟨m, hm⟩
              have hKne : ∀ z ∈ K.1, z ≠ 0 := by
                exact orbitFin020_ne_zero_of_disjoint023 a
                  (by simpa [K, L] using hdisj)
              have hKzero : K.1.count 0 = 0 := by
                apply Multiset.count_eq_zero.mpr
                intro hz
                exact hKne 0 hz rfl
              have hcountdec :=
                congrArg (fun z : Multiset ℂ => z.count 0) hdec
              simp only [Multiset.count_add, hKzero, zero_add] at hcountdec
              have hcarddec := congrArg Multiset.card hdec
              simp only [Multiset.card_add] at hcarddec
              have hwidth_eq : K.card + r.card + r.count 0 = 2 * e := by
                simpa [hcarddec, hcountdec] using htwidth
              have hme : m ≤ e := by
                omega
              have hKcard : K.card = 2 * m := by
                calc
                  K.card = m + m := hm
                  _ = 2 * m := by omega
              have hwidth_eq' : 2 * m + r.card + r.count 0 = 2 * e := by
                rw [← hKcard]
                exact hwidth_eq
              have hdouble : 2 * m + (r.card + r.count 0) = 2 * e := by
                simpa [Nat.add_assoc] using hwidth_eq'
              have hwidthr : r.card + r.count 0 = 2 * (e - m) :=
                width_sub_double023 (r.card + r.count 0) m e
                  hdouble hme
              obtain ⟨u, husum, huj, hui, huw, huc⟩ :=
                ih r.card hrcard r (e - m) rfl hrj hri hwidthr
              have hKcoeff := orbit_even_reflectCoeff023 a ha0 ⟨m, hm⟩
              have hhalf : K.card / 2 = m := by omega
              rw [hhalf] at hKcoeff
              have hqcard : (K.1 + u).card = K.card + u.card := by
                simp
              refine ⟨K.1 + u, ?_, ?_, ?_, ?_, ?_⟩
              · calc
                  t + Multiset.map (starRingEnd ℂ) t =
                      (K.1 + r) +
                        Multiset.map (starRingEnd ℂ) (K.1 + r) := by
                          rw [hdec]
                  _ = (K.1 + Multiset.map (starRingEnd ℂ) K.1) +
                        (r + Multiset.map (starRingEnd ℂ) r) := by
                          rw [Multiset.map_add, hKstar]
                          ac_rfl
                  _ = (K.1 + Multiset.map (starRingEnd ℂ) K.1) +
                        (u + Multiset.map (starRingEnd ℂ) u) := by
                          rw [husum]
                  _ = (K.1 + u) +
                        Multiset.map (starRingEnd ℂ) (K.1 + u) := by
                          rw [Multiset.map_add, hKstar]
                          ac_rfl
              · rw [Multiset.map_add, hKj, huj]
              · rw [Multiset.map_add, hKi, hui]
              · simp only [Multiset.card_add, Multiset.count_add, hKzero]
                omega
              · calc
                  reflectCoeff022 (K.1 + u) =
                      reflectCoeff022 K.1 * reflectCoeff022 u :=
                    reflectCoeff_add023 K.1 u
                  _ = (-1 : ℂ) ^ m *
                      (-1 : ℂ) ^ (e - m + u.card) := by
                        rw [hKcoeff, huc]
                  _ = (-1 : ℂ) ^ (e + (K.1 + u).card) := by
                        rw [hqcard]
                        calc
                          (-1 : ℂ) ^ m *
                              (-1 : ℂ) ^ (e - m + u.card) =
                              (-1 : ℂ) ^ (m + (e - m + u.card)) :=
                            (pow_add _ _ _).symm
                          _ = (-1 : ℂ) ^ (e + u.card) := by
                            congr 1
                            omega
                          _ = (-1 : ℂ) ^
                              ((e + u.card) + (m + m)) := by
                            calc
                              (-1 : ℂ) ^ (e + u.card) =
                                  (-1 : ℂ) ^ (e + u.card) * 1 := by ring
                              _ = (-1 : ℂ) ^ (e + u.card) *
                                  (-1 : ℂ) ^ (m + m) := by
                                rw [neg_one_pow_even023]
                              _ = (-1 : ℂ) ^
                                  ((e + u.card) + (m + m)) :=
                                (pow_add _ _ _).symm
                          _ = (-1 : ℂ) ^ (e + (K.card + u.card)) := by
                            rw [hm]
                            congr 1
                            omega
          · have hinter : ∃ z, z ∈ K ∧ z ∈ L := by
              by_contra hno
              apply hdisj
              refine Finset.disjoint_left.mpr ?_
              intro z hzK hzL
              exact hno ⟨z, hzK, hzL⟩
            have hstarA0 : (starRingEnd ℂ) a ∈ orbitFin020 a := by
              exact star_mem_of_orbit_intersection020 a (by
                simpa [K, L] using hinter)
            have hKLfin : L = K := by
              simpa [K, L] using
                orbitStarFin020_eq_orbit_of_overlap020 a hstarA0
            have hKLval : L.1 = K.1 :=
              congrArg (fun F : Finset ℂ => F.1) hKLfin
            have hstarK : Multiset.map (starRingEnd ℂ) K.1 = K.1 :=
              hKstar.symm.trans hKLval
            have hKfixed : ∀ z ∈ K.1,
                (starRingEnd ℂ) z = z := by
              simpa [K] using star_fixed_on_orbit_of_overlap020 a hstarA0
            by_cases ha0 : a = 0
            · have hKzero_set : K = ({0} : Finset ℂ) := by
                subst a
                simp [K, orbitFin020]
              have hKzero : K.1.count 0 = 1 := by
                rw [hKzero_set]
                simp
              have hKcard : K.card = 1 := by
                rw [hKzero_set]
                simp
              have hcountdec :=
                congrArg (fun z : Multiset ℂ => z.count 0) hdec
              simp only [Multiset.count_add, hKzero] at hcountdec
              have hcarddec := congrArg Multiset.card hdec
              simp only [Multiset.card_add] at hcarddec
              have hepos : 1 ≤ e := by
                omega
              have hwidth_eq : K.card + r.card + (1 + r.count 0) = 2 * e := by
                simpa [hcarddec, hcountdec] using htwidth
              have hwidth_eq' := hwidth_eq
              rw [hKcard] at hwidth_eq'
              have hdouble : 2 * 1 + (r.card + r.count 0) = 2 * e := by
                omega
              have hwidthr : r.card + r.count 0 = 2 * (e - 1) :=
                width_sub_double023 (r.card + r.count 0) 1 e
                  hdouble hepos
              obtain ⟨u, husum, huj, hui, huw, huc⟩ :=
                ih r.card hrcard r (e - 1) rfl hrj hri hwidthr
              have hKval : K.1 = ({0} : Multiset ℂ) := by
                simpa using congrArg (fun F : Finset ℂ => F.1) hKzero_set
              have hKcoeff : reflectCoeff022 K.1 = 1 := by
                rw [hKval]
                have hfilter :
                    ({0} : Multiset ℂ).filter (fun z : ℂ => z ≠ 0) = 0 := by
                  simp
                simp [reflectCoeff022, nonzeroProduct022, hfilter]
              have hqcard : (K.1 + u).card = K.card + u.card := by
                simp
              refine ⟨K.1 + u, ?_, ?_, ?_, ?_, ?_⟩
              · calc
                  t + Multiset.map (starRingEnd ℂ) t =
                      (K.1 + r) +
                        Multiset.map (starRingEnd ℂ) (K.1 + r) := by
                          rw [hdec]
                  _ = (K.1 + Multiset.map (starRingEnd ℂ) K.1) +
                        (r + Multiset.map (starRingEnd ℂ) r) := by
                          rw [Multiset.map_add, hstarK]
                          ac_rfl
                  _ = (K.1 + Multiset.map (starRingEnd ℂ) K.1) +
                        (u + Multiset.map (starRingEnd ℂ) u) := by
                          rw [husum]
                  _ = (K.1 + u) +
                        Multiset.map (starRingEnd ℂ) (K.1 + u) := by
                          rw [Multiset.map_add, hstarK]
                          ac_rfl
              · rw [Multiset.map_add, hKj, huj]
              · rw [Multiset.map_add, hKi, hui]
              · simp only [Multiset.card_add, Multiset.count_add, hKzero]
                omega
              · calc
                  reflectCoeff022 (K.1 + u) =
                      reflectCoeff022 K.1 * reflectCoeff022 u :=
                    reflectCoeff_add023 K.1 u
                  _ = (-1 : ℂ) ^ (e - 1 + u.card) := by
                    rw [hKcoeff, huc]
                    norm_num
                  _ = (-1 : ℂ) ^ (e + (K.1 + u).card) := by
                    rw [hqcard, hKcard]
                    rw [show e + (1 + u.card) =
                        (e - 1 + u.card) + 2 by omega]
                    rw [neg_one_pow_add_two023]
            · have hKne : ∀ z ∈ K.1, z ≠ 0 :=
                orbitFin020_ne_zero_of_ne_zero023 a ha0
              have hKzero : K.1.count 0 = 0 := by
                apply Multiset.count_eq_zero.mpr
                intro hz
                exact hKne 0 hz rfl
              have hKeven : Even K.card :=
                orbit_overlap_even023 a ha0 hstarA0
              rcases hKeven with ⟨m, hm⟩
              have hcountdec :=
                congrArg (fun z : Multiset ℂ => z.count 0) hdec
              simp only [Multiset.count_add, hKzero, zero_add] at hcountdec
              have hcarddec := congrArg Multiset.card hdec
              simp only [Multiset.card_add] at hcarddec
              have hwidth_eq : K.card + r.card + r.count 0 = 2 * e := by
                simpa [hcarddec, hcountdec] using htwidth
              have hme : m ≤ e := by
                omega
              have hKcard : K.card = 2 * m := by
                calc
                  K.card = m + m := hm
                  _ = 2 * m := by omega
              have hwidth_eq' : 2 * m + r.card + r.count 0 = 2 * e := by
                rw [← hKcard]
                exact hwidth_eq
              have hdouble : 2 * m + (r.card + r.count 0) = 2 * e := by
                simpa [Nat.add_assoc] using hwidth_eq'
              have hwidthr : r.card + r.count 0 = 2 * (e - m) :=
                width_sub_double023 (r.card + r.count 0) m e
                  hdouble hme
              obtain ⟨u, husum, huj, hui, huw, huc⟩ :=
                ih r.card hrcard r (e - m) rfl hrj hri hwidthr
              have hKcoeff := orbit_even_reflectCoeff023 a ha0 ⟨m, hm⟩
              have hhalf : K.card / 2 = m := by omega
              rw [hhalf] at hKcoeff
              have hqcard : (K.1 + u).card = K.card + u.card := by
                simp
              refine ⟨K.1 + u, ?_, ?_, ?_, ?_, ?_⟩
              · calc
                  t + Multiset.map (starRingEnd ℂ) t =
                      (K.1 + r) +
                        Multiset.map (starRingEnd ℂ) (K.1 + r) := by
                          rw [hdec]
                  _ = (K.1 + Multiset.map (starRingEnd ℂ) K.1) +
                        (r + Multiset.map (starRingEnd ℂ) r) := by
                          rw [Multiset.map_add, hstarK]
                          ac_rfl
                  _ = (K.1 + Multiset.map (starRingEnd ℂ) K.1) +
                        (u + Multiset.map (starRingEnd ℂ) u) := by
                          rw [husum]
                  _ = (K.1 + u) +
                        Multiset.map (starRingEnd ℂ) (K.1 + u) := by
                          rw [Multiset.map_add, hstarK]
                          ac_rfl
              · rw [Multiset.map_add, hKj, huj]
              · rw [Multiset.map_add, hKi, hui]
              · simp only [Multiset.card_add, Multiset.count_add, hKzero]
                omega
              · calc
                  reflectCoeff022 (K.1 + u) =
                      reflectCoeff022 K.1 * reflectCoeff022 u :=
                    reflectCoeff_add023 K.1 u
                  _ = (-1 : ℂ) ^ m *
                      (-1 : ℂ) ^ (e - m + u.card) := by
                        rw [hKcoeff, huc]
                  _ = (-1 : ℂ) ^ (e + (K.1 + u).card) := by
                        rw [hqcard]
                        calc
                          (-1 : ℂ) ^ m *
                              (-1 : ℂ) ^ (e - m + u.card) =
                              (-1 : ℂ) ^ (m + (e - m + u.card)) :=
                            (pow_add _ _ _).symm
                          _ = (-1 : ℂ) ^ (e + u.card) := by
                            congr 1
                            omega
                          _ = (-1 : ℂ) ^
                              ((e + u.card) + (m + m)) := by
                            calc
                              (-1 : ℂ) ^ (e + u.card) =
                                  (-1 : ℂ) ^ (e + u.card) * 1 := by ring
                              _ = (-1 : ℂ) ^ (e + u.card) *
                                  (-1 : ℂ) ^ (m + m) := by
                                rw [neg_one_pow_even023]
                              _ = (-1 : ℂ) ^
                                  ((e + u.card) + (m + m)) :=
                                (pow_add _ _ _).symm
                          _ = (-1 : ℂ) ^ (e + (K.card + u.card)) := by
                            rw [hm]
                            congr 1
                            omega
  exact hP q.card q d rfl hqj hqi hwidth

theorem cayley_reflect_transport_sign023
    (B : Polynomial ℝ) (d : ℕ)
    (hB : B.natDegree ≤ d)
    (s : ℝ)
    (hreflect :
      (cayleyNumerator127 B d).reflect (2 * d) =
        Polynomial.C s * cayleyNumerator127 B d) :
    cayleyNumerator127
          (B.comp (-(Polynomial.X : Polynomial ℝ))) d =
        Polynomial.C s * cayleyNumerator127 B d := by
  let E : Polynomial ℝ := cayleyNumerator127 B d
  let S : Polynomial ℝ := cayleyNumerator127
      (B.comp (-(Polynomial.X : Polynomial ℝ))) d
  have hEdeg : E.natDegree ≤ 2 * d := by
    exact cayleyNumerator_natDegree_le_twice127 B d
  have hcomp : (B.comp (-(Polynomial.X : Polynomial ℝ))).natDegree ≤ d := by
    calc
      (B.comp (-(Polynomial.X : Polynomial ℝ))).natDegree ≤
          B.natDegree * (-(Polynomial.X : Polynomial ℝ)).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ d := by simpa using hB
  apply Polynomial.eq_of_infinite_eval_eq
  have hinf : (Set.Ioi (0 : ℝ)).Infinite := Set.Ioi_infinite 0
  refine hinf.mono ?_
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  letI : Invertible t := invertibleOfNonzero ht0
  have hstep := Polynomial.eval₂_reflect_mul_pow
    (RingHom.id ℝ) (t⁻¹) (2 * d) E hEdeg
  simp only [invOf_eq_inv] at hstep
  have hmul :
      Polynomial.eval t (E.reflect (2 * d)) * (t⁻¹) ^ (2 * d) =
        Polynomial.eval (t⁻¹) E := by
    simpa using hstep
  have hpow : (t⁻¹) ^ (2 * d) * t ^ (2 * d) = (1 : ℝ) := by
    rw [← mul_pow]
    simp [ht0]
  have hrecip :
      Polynomial.eval (t⁻¹) E * t ^ (2 * d) =
        s * Polynomial.eval t E := by
    calc
      Polynomial.eval (t⁻¹) E * t ^ (2 * d) =
          (Polynomial.eval t (E.reflect (2 * d)) *
            (t⁻¹) ^ (2 * d)) * t ^ (2 * d) := by rw [hmul]
      _ = Polynomial.eval t (E.reflect (2 * d)) := by
        rw [mul_assoc, hpow, mul_one]
      _ = Polynomial.eval t (Polynomial.C s * E) := by
        rw [show E = cayleyNumerator127 B d by rfl]
        exact congrArg (fun z => Polynomial.eval t z) hreflect
      _ = s * Polynomial.eval t E := by
        simp [Polynomial.eval_mul]
  have hden : (1 + t ^ 2 : ℝ) ≠ 0 := by
    nlinarith [sq_nonneg t]
  have hinvarg :
      (1 - (t⁻¹) ^ 2) / (1 + (t⁻¹) ^ 2) =
        -((1 - t ^ 2) / (1 + t ^ 2)) := by
    field_simp [ht0, hden]
    ring
  have hinvbase :
      1 + (t⁻¹) ^ 2 = (1 + t ^ 2) / t ^ 2 := by
    field_simp [ht0]
    ring
  have hinvscale :
      (1 + (t⁻¹) ^ 2) ^ d * t ^ (2 * d) =
        (1 + t ^ 2) ^ d := by
    rw [hinvbase, div_pow]
    have htpow : t ^ (2 * d) = (t ^ 2) ^ d := by
      rw [pow_mul]
    rw [htpow]
    field_simp [ht0, hden]
  have hS_eval :
      Polynomial.eval t S =
        Polynomial.eval (-((1 - t ^ 2) / (1 + t ^ 2))) B *
            (1 + t ^ 2) ^ d := by
    dsimp [S]
    rw [cayley_eval_homogenized127
      (B.comp (-(Polynomial.X : Polynomial ℝ))) d hcomp t]
    rw [Polynomial.eval_comp]
    simp [Polynomial.eval_neg]
  have hE_eval :
      Polynomial.eval t E =
        Polynomial.eval ((1 - t ^ 2) / (1 + t ^ 2)) B *
            (1 + t ^ 2) ^ d := by
    exact cayley_eval_homogenized127 B d hB t
  have hE_inv :
      Polynomial.eval (t⁻¹) E =
        Polynomial.eval (-((1 - t ^ 2) / (1 + t ^ 2))) B *
            (1 + (t⁻¹) ^ 2) ^ d := by
    dsimp [E]
    rw [cayley_eval_homogenized127 B d hB (t⁻¹), hinvarg]
  have hrecip' := hrecip
  rw [hE_inv, hE_eval] at hrecip'
  have hinvprod :
      Polynomial.eval (-((1 - t ^ 2) / (1 + t ^ 2))) B *
          (1 + t⁻¹ ^ 2) ^ d * t ^ (2 * d) =
        Polynomial.eval (-((1 - t ^ 2) / (1 + t ^ 2))) B *
          (1 + t ^ 2) ^ d := by
    calc
      Polynomial.eval (-((1 - t ^ 2) / (1 + t ^ 2))) B *
          (1 + t⁻¹ ^ 2) ^ d * t ^ (2 * d) =
          Polynomial.eval (-((1 - t ^ 2) / (1 + t ^ 2))) B *
            ((1 + t⁻¹ ^ 2) ^ d * t ^ (2 * d)) := by ring
      _ = Polynomial.eval (-((1 - t ^ 2) / (1 + t ^ 2))) B *
            (1 + t ^ 2) ^ d := by rw [hinvscale]
  have hrecip'' :
      Polynomial.eval (-((1 - t ^ 2) / (1 + t ^ 2))) B *
          (1 + t ^ 2) ^ d =
        s *
          (Polynomial.eval ((1 - t ^ 2) / (1 + t ^ 2)) B *
            (1 + t ^ 2) ^ d) :=
    hinvprod.symm.trans hrecip'
  change Polynomial.eval t
      (cayleyNumerator127 (B.comp (-(Polynomial.X : Polynomial ℝ))) d) =
      Polynomial.eval t
        (Polynomial.C s * cayleyNumerator127 B d)
  rw [hS_eval]
  change Polynomial.eval (-((1 - t ^ 2) / (1 + t ^ 2))) B *
      (1 + t ^ 2) ^ d =
    Polynomial.eval t (Polynomial.C s * E)
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  rw [hE_eval]
  exact hrecip''

theorem cayleyNumerator_smul023
    (B : Polynomial ℝ) (d : ℕ) (s : ℝ)
    (hB : B.natDegree ≤ d) :
    cayleyNumerator127 (Polynomial.C s * B) d =
      Polynomial.C s * cayleyNumerator127 B d := by
  have hsb : (Polynomial.C s * B).natDegree ≤ d := by
    calc
      (Polynomial.C s * B).natDegree ≤
          (Polynomial.C s).natDegree + B.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ d := by simpa using hB
  apply Polynomial.funext
  intro t
  rw [cayley_eval_homogenized127 (Polynomial.C s * B) d hsb t]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [cayley_eval_homogenized127 B d hB t]
  ring

theorem cayley_reflect_comp_eq023
    (B : Polynomial ℝ) (d : ℕ) (s : ℝ)
    (hB : B.natDegree ≤ d)
    (hreflect :
      (cayleyNumerator127 B d).reflect (2 * d) =
        Polynomial.C s * cayleyNumerator127 B d) :
    B.comp (-(Polynomial.X : Polynomial ℝ)) = Polynomial.C s * B := by
  have hcomp : (B.comp (-(Polynomial.X : Polynomial ℝ))).natDegree ≤ d := by
    calc
      (B.comp (-(Polynomial.X : Polynomial ℝ))).natDegree ≤
          B.natDegree * (-(Polynomial.X : Polynomial ℝ)).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ d := by simpa using hB
  have htransport := cayley_reflect_transport_sign023 B d hB s hreflect
  have hsmul := cayleyNumerator_smul023 B d s hB
  have hsb : (Polynomial.C s * B).natDegree ≤ d := by
    calc
      (Polynomial.C s * B).natDegree ≤
          (Polynomial.C s).natDegree + B.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ d := by simpa using hB
  exact cayleyNumerator_injective020
    (B.comp (-(Polynomial.X : Polynomial ℝ)))
    (Polynomial.C s * B) d hcomp hsb (htransport.trans hsmul.symm)

lemma reflect_succ_factor023
    (D : Polynomial ℝ) (N : ℕ) (hD : D.natDegree ≤ N) :
    D.reflect (N + 1) =
      D.reflect N * (Polynomial.X : Polynomial ℝ) := by
  have h := Polynomial.reflect_mul D (1 : Polynomial ℝ)
    (F := N) (G := 1) hD (by simp)
  simpa [Polynomial.reflect_one] using h

theorem odd_reflect_inner023
    (C O : Polynomial ℝ) (d : ℕ) (hdpos : 0 < d)
    (hOcal : O = Polynomial.C (2 : ℝ) * Polynomial.X *
      cayleyNumerator127 C (d - 1))
    (hOreflect : O.reflect (2 * d) =
      Polynomial.C (-((-1 : ℝ) ^ d)) * O) :
    (cayleyNumerator127 C (d - 1)).reflect (2 * (d - 1)) =
      Polynomial.C (-((-1 : ℝ) ^ d)) *
        cayleyNumerator127 C (d - 1) := by
  let D : Polynomial ℝ := cayleyNumerator127 C (d - 1)
  have hDdeg : D.natDegree ≤ 2 * (d - 1) := by
    exact cayleyNumerator_natDegree_le_twice127 C (d - 1)
  have hDdeg' : D.natDegree ≤ 2 * d - 1 := by
    exact hDdeg.trans (by omega)
  have hXdeg :
      (Polynomial.C (2 : ℝ) * Polynomial.X).natDegree ≤ 1 := by
    calc
      (Polynomial.C (2 : ℝ) * Polynomial.X).natDegree ≤
          (Polynomial.C (2 : ℝ)).natDegree + Polynomial.X.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 1 := by simp
  have hfactor := Polynomial.reflect_mul
    (Polynomial.C (2 : ℝ) * Polynomial.X) D
    (F := 1) (G := 2 * d - 1) hXdeg hDdeg'
  have hwidth : 1 + (2 * d - 1) = 2 * d := by omega
  rw [hwidth] at hfactor
  have hOreflect' := hOreflect
  rw [hOcal] at hOreflect'
  have hC2reflect :
      (Polynomial.C (2 : ℝ) * Polynomial.X).reflect 1 =
        Polynomial.C (2 : ℝ) := by
    simp
  rw [hfactor, hC2reflect] at hOreflect'
  have hDsucc :
      D.reflect (2 * d - 1) =
        Polynomial.C (-((-1 : ℝ) ^ d)) * Polynomial.X * D := by
    have hcancel :
        Polynomial.C (2 : ℝ) * D.reflect (2 * d - 1) =
          Polynomial.C (2 : ℝ) *
            (Polynomial.C (-((-1 : ℝ) ^ d)) * Polynomial.X * D) := by
      calc
        Polynomial.C (2 : ℝ) * D.reflect (2 * d - 1) =
            Polynomial.C (-((-1 : ℝ) ^ d)) *
              (Polynomial.C (2 : ℝ) * Polynomial.X * D) := by
                simpa [D] using hOreflect'
        _ = Polynomial.C (2 : ℝ) *
            (Polynomial.C (-((-1 : ℝ) ^ d)) * Polynomial.X * D) := by
              ring
    exact mul_left_cancel₀ (by norm_num) hcancel
  have hDsucc' : D.reflect ((2 * (d - 1)) + 1) =
      D.reflect (2 * (d - 1)) * Polynomial.X := by
    exact reflect_succ_factor023 D (2 * (d - 1)) hDdeg
  have hDreflect :
      D.reflect (2 * (d - 1)) =
        Polynomial.C (-((-1 : ℝ) ^ d)) * D := by
    have hx :
        D.reflect (2 * (d - 1)) * Polynomial.X =
          (Polynomial.C (-((-1 : ℝ) ^ d)) * D) * Polynomial.X := by
      calc
        D.reflect (2 * (d - 1)) * Polynomial.X =
            D.reflect ((2 * (d - 1)) + 1) := hDsucc'.symm
        _ = D.reflect (2 * d - 1) := by congr 1; omega
        _ = Polynomial.C (-((-1 : ℝ) ^ d)) * Polynomial.X * D := hDsucc
        _ = (Polynomial.C (-((-1 : ℝ) ^ d)) * D) * Polynomial.X := by
              ring
    exact mul_right_cancel₀ Polynomial.X_ne_zero hx
  simpa [D] using hDreflect

theorem interval_completion_witness023
    (input : GeneralRealQSPPolynomial127) :
    Nonempty (IntervalCompletionWitness127 input) := by
  by_cases hdpos : 0 < input.degree
  · let p : Polynomial ℝ := cayleyResidual127 input
    have hres : (intervalResidual127 input).natDegree ≤
        2 * input.degree :=
      intervalResidual127_natDegree_le_twice127 input
    have hnonneg : ∀ x : ℝ, -1 ≤ x → x ≤ 1 →
        0 ≤ Polynomial.eval x (intervalResidual127 input) := by
      intro x hxlo hxhi
      exact intervalResidual127_nonnegative input hxlo hxhi
    by_cases hpzero : p = 0
    · have hcnum0 : cayleyNumerator127
          (0 : Polynomial ℝ) (2 * input.degree) = 0 := by
        simp [cayleyNumerator127]
      have hreszero : intervalResidual127 input = 0 := by
        apply cayleyNumerator_injective020
          (intervalResidual127 input) 0 (2 * input.degree)
          hres (by simp)
        simpa [p, cayleyResidual127, hcnum0] using hpzero
      refine ⟨⟨0, 0, ?_, ?_, ?_, ?_, ?_⟩⟩
      · simp [hreszero]
      · simp
      · simp
      · intro x
        simp
      · intro x
        simp
    · have hpcomplex : cayleyResidualComplex127 input ≠ 0 := by
        intro hz
        apply hpzero
        change cayleyResidual127 input = 0
        apply (Polynomial.map_eq_zero_iff Complex.ofRealHom.injective).mp
        simpa [cayleyResidualComplex127] using hz
      obtain ⟨q, hroots, hqj, hqi⟩ :=
        cayley_root_partition_with_inv020 input
      have hroots' : (p.map Complex.ofRealHom).roots =
          q + Multiset.map (starRingEnd ℂ) q := by
        simpa [p, cayleyResidualComplex127, cayleyResidual127] using hroots
      have hwidth := cayley_q_zero_balance021 input hpcomplex hroots
      have hcoeff : 0 ≤ p.leadingCoeff := by
        exact leadingCoeff_nonneg_of_nonnegative_global127 p hpzero
          (cayley_nonnegative127
            (intervalResidual127 input) (2 * input.degree) hres hnonneg)
      obtain ⟨q', hsumq, hqj', hqi', hwidth', htarget⟩ :=
        orient_half_target023 q input.degree hqj hqi hwidth
      have hroots'' : (p.map Complex.ofRealHom).roots =
          q' + Multiset.map (starRingEnd ℂ) q' :=
        hroots'.trans hsumq
      obtain ⟨E, O, hEO, hEeven, hOodd, hEreflect, hOreflect,
          hEdeg, hOdeg⟩ := spectralFactor_targeted_components023
        p input.degree hpzero hcoeff hwidth' hroots'' hqj' hqi' htarget
      obtain ⟨B, hBcal, hBdeg⟩ :=
        even_inverse_cayley020 E input.degree hEdeg hEeven
      obtain ⟨C, hOcal, hCdeg⟩ :=
        odd_inverse_cayley020 O input.degree hdpos hOdeg hOodd
      have hBnat : B.natDegree ≤ input.degree :=
        (Polynomial.natDegree_le_iff_degree_le).mpr hBdeg
      have hCnat : C.natDegree ≤ input.degree - 1 :=
        (Polynomial.natDegree_le_iff_degree_le).mpr hCdeg
      have hBreflect :
          (cayleyNumerator127 B input.degree).reflect
              (2 * input.degree) =
            Polynomial.C ((-1 : ℝ) ^ input.degree) *
              cayleyNumerator127 B input.degree := by
        rw [hBcal]
        exact hEreflect
      have hBcomp := cayley_reflect_comp_eq023 B input.degree
        ((-1 : ℝ) ^ input.degree) hBnat hBreflect
      have hBpar : ∀ x : ℝ,
          Polynomial.eval (-x) B =
            if input.degree % 2 = 0 then Polynomial.eval x B
            else -Polynomial.eval x B := by
        intro x
        have hx := congrArg (fun z : Polynomial ℝ => Polynomial.eval x z)
          hBcomp
        rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C]
          at hx
        rcases Nat.even_or_odd input.degree with he | ho
        · have hpow : (-1 : ℝ) ^ input.degree = 1 := by
            rcases he with ⟨m, hm⟩
            rw [hm]
            simp
          have hmod : input.degree % 2 = 0 := by
            rcases he with ⟨m, hm⟩
            omega
          simpa [hmod, hpow] using hx
        · have hpow : (-1 : ℝ) ^ input.degree = -1 := by
            rcases ho with ⟨m, hm⟩
            rw [hm]
            norm_num [pow_add]
          have hmod : input.degree % 2 ≠ 0 := by
            rcases ho with ⟨m, hm⟩
            omega
          simpa [hmod, hpow] using hx
      have hCreflect :
          (cayleyNumerator127 C (input.degree - 1)).reflect
              (2 * (input.degree - 1)) =
            Polynomial.C (-((-1 : ℝ) ^ input.degree)) *
              cayleyNumerator127 C (input.degree - 1) := by
        exact odd_reflect_inner023 C O input.degree hdpos hOcal hOreflect
      have hCcomp := cayley_reflect_comp_eq023 C (input.degree - 1)
        (-((-1 : ℝ) ^ input.degree)) hCnat hCreflect
      have hCpar : ∀ x : ℝ,
          Polynomial.eval (-x) C =
            if input.degree % 2 = 0 then -Polynomial.eval x C
            else Polynomial.eval x C := by
        intro x
        have hx := congrArg (fun z : Polynomial ℝ => Polynomial.eval x z)
          hCcomp
        rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C]
          at hx
        rcases Nat.even_or_odd input.degree with he | ho
        · have hpow : (-1 : ℝ) ^ input.degree = 1 := by
            rcases he with ⟨m, hm⟩
            rw [hm]
            simp
          have hmod : input.degree % 2 = 0 := by
            rcases he with ⟨m, hm⟩
            omega
          simpa [hmod, hpow] using hx
        · have hpow : (-1 : ℝ) ^ input.degree = -1 := by
            rcases ho with ⟨m, hm⟩
            rw [hm]
            norm_num [pow_add]
          have hmod : input.degree % 2 ≠ 0 := by
            rcases ho with ⟨m, hm⟩
            omega
          simpa [hmod, hpow] using hx
      have hdecomp := cayleyNumerator_decomposition020 B C input.degree
        hdpos hBnat hCnat
      have hsq : (B ^ 2).natDegree ≤ 2 * input.degree := by
        calc
          (B ^ 2).natDegree ≤ 2 * B.natDegree :=
            Polynomial.natDegree_pow_le
          _ ≤ 2 * input.degree := Nat.mul_le_mul_left 2 hBnat
      have hleft :
          ((1 : Polynomial ℝ) - Polynomial.X ^ 2).natDegree ≤ 2 := by
        calc
          ((1 : Polynomial ℝ) - Polynomial.X ^ 2).natDegree ≤
              max (1 : Polynomial ℝ).natDegree (Polynomial.X ^ 2).natDegree :=
            Polynomial.natDegree_sub_le _ _
          _ = 2 := by simp
      have hCsq : (C ^ 2).natDegree ≤
          2 * (input.degree - 1) := by
        calc
          (C ^ 2).natDegree ≤ 2 * C.natDegree :=
            Polynomial.natDegree_pow_le
          _ ≤ 2 * (input.degree - 1) := Nat.mul_le_mul_left 2 hCnat
      have hterm :
          (((1 : Polynomial ℝ) - Polynomial.X ^ 2) * C ^ 2).natDegree ≤
            2 * input.degree := by
        calc
          (((1 : Polynomial ℝ) - Polynomial.X ^ 2) * C ^ 2).natDegree ≤
              ((1 : Polynomial ℝ) - Polynomial.X ^ 2).natDegree +
                (C ^ 2).natDegree := Polynomial.natDegree_mul_le
          _ ≤ 2 + 2 * (input.degree - 1) := add_le_add hleft hCsq
          _ = 2 * input.degree := by omega
      have hfinal :
          (B ^ 2 + ((1 : Polynomial ℝ) - Polynomial.X ^ 2) * C ^ 2).natDegree ≤
            2 * input.degree := by
        calc
          (B ^ 2 + ((1 : Polynomial ℝ) - Polynomial.X ^ 2) * C ^ 2).natDegree ≤
              max (B ^ 2).natDegree
                (((1 : Polynomial ℝ) - Polynomial.X ^ 2) * C ^ 2).natDegree :=
            Polynomial.natDegree_add_le _ _
          _ ≤ 2 * input.degree := max_le hsq hterm
      have hpEq :
          cayleyNumerator127 (intervalResidual127 input)
              (2 * input.degree) =
            cayleyNumerator127
              (B ^ 2 + ((1 : Polynomial ℝ) - Polynomial.X ^ 2) * C ^ 2)
              (2 * input.degree) := by
        calc
          cayleyNumerator127 (intervalResidual127 input)
              (2 * input.degree) = E ^ 2 + O ^ 2 := by
                simpa [p, cayleyResidual127] using hEO
          _ = (cayleyNumerator127 B input.degree) ^ 2 + O ^ 2 := by
                rw [hBcal]
          _ = (cayleyNumerator127 B input.degree) ^ 2 +
              (Polynomial.C (2 : ℝ) * Polynomial.X *
                cayleyNumerator127 C (input.degree - 1)) ^ 2 := by
                rw [hOcal]
          _ = cayleyNumerator127
              (B ^ 2 + ((1 : Polynomial ℝ) - Polynomial.X ^ 2) * C ^ 2)
              (2 * input.degree) := hdecomp.symm
      have hidentity := cayleyNumerator_injective020
        (intervalResidual127 input)
        (B ^ 2 + ((1 : Polynomial ℝ) - Polynomial.X ^ 2) * C ^ 2)
        (2 * input.degree) hres hfinal hpEq
      have hCstrict : C.degree < (input.degree : WithBot ℕ) :=
        lt_of_le_of_lt hCdeg (by
          exact_mod_cast (show input.degree - 1 < input.degree by omega))
      exact ⟨⟨B, C, hidentity, hBdeg, hCstrict, hBpar, hCpar⟩⟩
  · have hd0 : input.degree = 0 := Nat.eq_zero_of_not_pos hdpos
    have hpdeg : input.polynomial.natDegree ≤ 0 := by
      simpa [hd0] using input.degree_bound
    have hpconst : input.polynomial =
        Polynomial.C (input.polynomial.coeff 0) := by
      exact Polynomial.eq_C_of_natDegree_le_zero hpdeg
    let a : ℝ := input.polynomial.coeff 0
    have heval : ∀ x : ℝ, Polynomial.eval x input.polynomial = a := by
      intro x
      rw [hpconst]
      simp [a]
    have habs := input.bounded_on_unitInterval 0 (by norm_num) (by norm_num)
    have ha : |a| ≤ 1 := by
      simpa [heval 0, a] using habs
    have habounds : -1 ≤ a ∧ a ≤ 1 := abs_le.mp ha
    have hnonneg : 0 ≤ 1 - a ^ 2 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]
    let B : Polynomial ℝ := Polynomial.C (Real.sqrt (1 - a ^ 2))
    have hres : intervalResidual127 input = B ^ 2 := by
      apply Polynomial.funext
      intro x
      rw [intervalResidual127_eval, heval, Polynomial.eval_pow]
      simp [B, a, Real.sq_sqrt hnonneg]
    refine ⟨⟨B, 0, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp [hres]
    · rw [hd0]
      dsimp [B]
      exact Polynomial.degree_C_le
    · simp
    · intro x
      simp [hd0, B]
    · intro x
      simp [hd0]

end
end SpectralSamplingProof.Analytic
