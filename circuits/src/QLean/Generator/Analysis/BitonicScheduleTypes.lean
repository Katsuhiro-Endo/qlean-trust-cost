import QLean.Generator.Analysis.QParameters
import QLean.Circuits.Foundation.BitonicNetworkAnalytic

/-!
# bitonic scheduleの回路非依存型

共有coreのlayout-independent schedule型と幅定理をQ側へ薄く公開する。
-/

namespace ProbabilityGeneratorQProof

/-- word数と履歴幅を型に持つ共有compare-exchange命令。 -/
abbrev TypedBitonicCompareExchange :=
  VerifiedCircuitCore.BitonicCompareExchangeWithHistory

/-- history割当前の共有compare-exchange命令。 -/
abbrev BareBitonicCompareExchange := VerifiedCircuitCore.BitonicCompareExchange

/-- 再帰bitonic networkのword数。 -/
abbrev recursiveBitonicWidth := VerifiedCircuitCore.bitonicNetworkWidth

/-- 再帰word数は`2^level`に等しい。 -/
theorem recursiveBitonicWidth_eq_pow (level : Nat) :
    recursiveBitonicWidth level = 2 ^ level :=
  VerifiedCircuitCore.bitonicNetworkWidth_eq_pow level

/-- 再帰word数は正である。 -/
theorem recursiveBitonicWidth_pos (level : Nat) :
    0 < recursiveBitonicWidth level :=
  VerifiedCircuitCore.bitonicNetworkWidth_pos level

end ProbabilityGeneratorQProof
