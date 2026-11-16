import PlattAssemblyKernel
import PlattCertificates.Count131072.C072944
import PlattCertificates.Count131072.C072945
import PlattCertificates.Count131072.C072946
import PlattCertificates.Count131072.C072947
import PlattCertificates.Count131072.C072948
import PlattCertificates.Count131072.C072949
import PlattCertificates.Count131072.C072950
import PlattCertificates.Count131072.C072951
import PlattCertificates.Count131072.C072952
import PlattCertificates.Count131072.C072953
import PlattCertificates.Count131072.C072954
import PlattCertificates.Count131072.C072955
import PlattCertificates.Count131072.C072956
import PlattCertificates.Count131072.C072957
import PlattCertificates.Count131072.C072958
import PlattCertificates.Count131072.C072959
import PlattCertificates.Count131072.C072960
import PlattCertificates.Count131072.C072961
import PlattCertificates.Count131072.C072962
import PlattCertificates.Count131072.C072963
import PlattCertificates.Count131072.C072964
import PlattCertificates.Count131072.C072965
import PlattCertificates.Count131072.C072966
import PlattCertificates.Count131072.C072967
import PlattCertificates.Count131072.C072968
import PlattCertificates.Count131072.C072969
import PlattCertificates.Count131072.C072970
import PlattCertificates.Count131072.C072971
import PlattCertificates.Count131072.C072972
import PlattCertificates.Count131072.C072973
import PlattCertificates.Count131072.C072974
import PlattCertificates.Count131072.C072975
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000092
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72944 : List PrefixCut := [⟨64,167415072,167415173⟩]
theorem checked72944 : checkPrefixCuts (2^48) 9564848129 10 Manual.Count131072.C072944.packed 64 cuts72944 = true := by
 decide +kernel
def cuts72945 : List PrefixCut := [⟨26,67977691,67977730⟩,
⟨64,169560978,169561073⟩]
theorem checked72945 : checkPrefixCuts (2^48) 9564979201 10 Manual.Count131072.C072945.packed 64 cuts72945 = true := by
 decide +kernel
def pointBounds72945 : List (Nat × Nat × Nat) := [(9565032448,116318798383326,116319188187528)]
theorem point_links_checked72945 : (cuts72945.take 1).map (fun c => (9564979201-1+2*2^10*c.k,116318730405635+c.lower,116319120209798+c.upper)) = pointBounds72945 := by
 decide +kernel
def cuts72946 : List PrefixCut := [⟨64,166586517,166586619⟩]
theorem checked72946 : checkPrefixCuts (2^48) 9565110273 10 Manual.Count131072.C072946.packed 64 cuts72946 = true := by
 decide +kernel
def cuts72947 : List PrefixCut := [⟨44,114764166,114764233⟩,
⟨64,167467041,167467139⟩]
theorem checked72947 : checkPrefixCuts (2^48) 9565241345 10 Manual.Count131072.C072947.packed 64 cuts72947 = true := by
 decide +kernel
def pointBounds72947 : List (Nat × Nat × Nat) := [(9565331456,116319181317296,116319571121723)]
theorem point_links_checked72947 : (cuts72947.take 1).map (fun c => (9565241345-1+2*2^10*c.k,116319066553130+c.lower,116319456357490+c.upper)) = pointBounds72947 := by
 decide +kernel
def cuts72948 : List PrefixCut := [⟨64,168582942,168583045⟩]
theorem checked72948 : checkPrefixCuts (2^48) 9565372417 10 Manual.Count131072.C072948.packed 64 cuts72948 = true := by
 decide +kernel
def cuts72949 : List PrefixCut := [⟨62,162489518,162489616⟩,
⟨64,167786134,167786235⟩]
theorem checked72949 : checkPrefixCuts (2^48) 9565503489 10 Manual.Count131072.C072949.packed 64 cuts72949 = true := by
 decide +kernel
def pointBounds72949 : List (Nat × Nat × Nat) := [(9565630464,116319565092631,116319954897290)]
theorem point_links_checked72949 : (cuts72949.take 1).map (fun c => (9565503489-1+2*2^10*c.k,116319402603113+c.lower,116319792407674+c.upper)) = pointBounds72949 := by
 decide +kernel
def cuts72950 : List PrefixCut := [⟨64,167224755,167224861⟩]
theorem checked72950 : checkPrefixCuts (2^48) 9565634561 10 Manual.Count131072.C072950.packed 64 cuts72950 = true := by
 decide +kernel
def cuts72951 : List PrefixCut := [⟨64,167369588,167369694⟩]
theorem checked72951 : checkPrefixCuts (2^48) 9565765633 10 Manual.Count131072.C072951.packed 64 cuts72951 = true := by
 decide +kernel
def cuts72952 : List PrefixCut := [⟨16,44254870,44254896⟩,
⟨64,168867956,168868060⟩]
theorem checked72952 : checkPrefixCuts (2^48) 9565896705 10 Manual.Count131072.C072952.packed 64 cuts72952 = true := by
 decide +kernel
def pointBounds72952 : List (Nat × Nat × Nat) := [(9565929472,116319949238460,116320339043360)]
theorem point_links_checked72952 : (cuts72952.take 1).map (fun c => (9565896705-1+2*2^10*c.k,116319904983590+c.lower,116320294788464+c.upper)) = pointBounds72952 := by
 decide +kernel
def cuts72953 : List PrefixCut := [⟨64,167982907,167983005⟩]
theorem checked72953 : checkPrefixCuts (2^48) 9566027777 10 Manual.Count131072.C072953.packed 64 cuts72953 = true := by
 decide +kernel
def cuts72954 : List PrefixCut := [⟨34,88036366,88036418⟩,
⟨64,166774227,166774331⟩]
theorem checked72954 : checkPrefixCuts (2^48) 9566158849 10 Manual.Count131072.C072954.packed 64 cuts72954 = true := by
 decide +kernel
def pointBounds72954 : List (Nat × Nat × Nat) := [(9566228480,116320329870819,116320719675947)]
theorem point_links_checked72954 : (cuts72954.take 1).map (fun c => (9566158849-1+2*2^10*c.k,116320241834453+c.lower,116320631639529+c.upper)) = pointBounds72954 := by
 decide +kernel
def cuts72955 : List PrefixCut := [⟨64,167831184,167831288⟩]
theorem checked72955 : checkPrefixCuts (2^48) 9566289921 10 Manual.Count131072.C072955.packed 64 cuts72955 = true := by
 decide +kernel
def cuts72956 : List PrefixCut := [⟨52,136464133,136464212⟩,
⟨64,167505245,167505341⟩]
theorem checked72956 : checkPrefixCuts (2^48) 9566420993 10 Manual.Count131072.C072956.packed 64 cuts72956 = true := by
 decide +kernel
def pointBounds72956 : List (Nat × Nat × Nat) := [(9566527488,116320712903997,116321102709360)]
theorem point_links_checked72956 : (cuts72956.take 1).map (fun c => (9566420993-1+2*2^10*c.k,116320576439864+c.lower,116320966245148+c.upper)) = pointBounds72956 := by
 decide +kernel
def cuts72957 : List PrefixCut := [⟨64,168620999,168621101⟩]
theorem checked72957 : checkPrefixCuts (2^48) 9566552065 10 Manual.Count131072.C072957.packed 64 cuts72957 = true := by
 decide +kernel
def cuts72958 : List PrefixCut := [⟨64,167177004,167177100⟩]
theorem checked72958 : checkPrefixCuts (2^48) 9566683137 10 Manual.Count131072.C072958.packed 64 cuts72958 = true := by
 decide +kernel
def cuts72959 : List PrefixCut := [⟨6,16182094,16182104⟩,
⟨64,169881521,169881616⟩]
theorem checked72959 : checkPrefixCuts (2^48) 9566814209 10 Manual.Count131072.C072959.packed 64 cuts72959 = true := by
 decide +kernel
def pointBounds72959 : List (Nat × Nat × Nat) := [(9566826496,116321095925206,116321485730794)]
theorem point_links_checked72959 : (cuts72959.take 1).map (fun c => (9566814209-1+2*2^10*c.k,116321079743112+c.lower,116321469548690+c.upper)) = pointBounds72959 := by
 decide +kernel
def cuts72960 : List PrefixCut := [⟨64,168466955,168467052⟩]
theorem checked72960 : checkPrefixCuts (2^48) 9566945281 10 Manual.Count131072.C072960.packed 64 cuts72960 = true := by
 decide +kernel
def cuts72961 : List PrefixCut := [⟨24,63284842,63284881⟩,
⟨64,168847125,168847227⟩]
theorem checked72961 : checkPrefixCuts (2^48) 9567076353 10 Manual.Count131072.C072961.packed 64 cuts72961 = true := by
 decide +kernel
def pointBounds72961 : List (Nat × Nat × Nat) := [(9567125504,116321481376430,116321871182239)]
theorem point_links_checked72961 : (cuts72961.take 1).map (fun c => (9567076353-1+2*2^10*c.k,116321418091588+c.lower,116321807897358+c.upper)) = pointBounds72961 := by
 decide +kernel
def cuts72962 : List PrefixCut := [⟨64,166638275,166638376⟩]
theorem checked72962 : checkPrefixCuts (2^48) 9567207425 10 Manual.Count131072.C072962.packed 64 cuts72962 = true := by
 decide +kernel
def cuts72963 : List PrefixCut := [⟨42,112473672,112473745⟩,
⟨64,171637419,171637528⟩]
theorem checked72963 : checkPrefixCuts (2^48) 9567338497 10 Manual.Count131072.C072963.packed 64 cuts72963 = true := by
 decide +kernel
def pointBounds72963 : List (Nat × Nat × Nat) := [(9567424512,116321866050660,116322255856706)]
theorem point_links_checked72963 : (cuts72963.take 1).map (fun c => (9567338497-1+2*2^10*c.k,116321753576988+c.lower,116322143382961+c.upper)) = pointBounds72963 := by
 decide +kernel
def cuts72964 : List PrefixCut := [⟨64,167545719,167545822⟩]
theorem checked72964 : checkPrefixCuts (2^48) 9567469569 10 Manual.Count131072.C072964.packed 64 cuts72964 = true := by
 decide +kernel
def cuts72965 : List PrefixCut := [⟨60,159747348,159747443⟩,
⟨64,170367679,170367780⟩]
theorem checked72965 : checkPrefixCuts (2^48) 9567600641 10 Manual.Count131072.C072965.packed 64 cuts72965 = true := by
 decide +kernel
def pointBounds72965 : List (Nat × Nat × Nat) := [(9567723520,116322252507474,116322642313754)]
theorem point_links_checked72965 : (cuts72965.take 1).map (fun c => (9567600641-1+2*2^10*c.k,116322092760126+c.lower,116322482566311+c.upper)) = pointBounds72965 := by
 decide +kernel
def cuts72966 : List PrefixCut := [⟨64,166923329,166923435⟩]
theorem checked72966 : checkPrefixCuts (2^48) 9567731713 10 Manual.Count131072.C072966.packed 64 cuts72966 = true := by
 decide +kernel
def cuts72967 : List PrefixCut := [⟨64,169215697,169215794⟩]
theorem checked72967 : checkPrefixCuts (2^48) 9567862785 10 Manual.Count131072.C072967.packed 64 cuts72967 = true := by
 decide +kernel
def cuts72968 : List PrefixCut := [⟨14,37567217,37567240⟩,
⟨64,169419304,169419407⟩]
theorem checked72968 : checkPrefixCuts (2^48) 9567993857 10 Manual.Count131072.C072968.packed 64 cuts72968 = true := by
 decide +kernel
def pointBounds72968 : List (Nat × Nat × Nat) := [(9568022528,116322636834048,116323026640560)]
theorem point_links_checked72968 : (cuts72968.take 1).map (fun c => (9567993857-1+2*2^10*c.k,116322599266831+c.lower,116322989073320+c.upper)) = pointBounds72968 := by
 decide +kernel
def cuts72969 : List PrefixCut := [⟨64,166710536,166710637⟩]
theorem checked72969 : checkPrefixCuts (2^48) 9568124929 10 Manual.Count131072.C072969.packed 64 cuts72969 = true := by
 decide +kernel
def cuts72970 : List PrefixCut := [⟨32,83163203,83163251⟩,
⟨64,167296603,167296699⟩]
theorem checked72970 : checkPrefixCuts (2^48) 9568256001 10 Manual.Count131072.C072970.packed 64 cuts72970 = true := by
 decide +kernel
def pointBounds72970 : List (Nat × Nat × Nat) := [(9568321536,116323018559874,116323408366615)]
theorem point_links_checked72970 : (cuts72970.take 1).map (fun c => (9568256001-1+2*2^10*c.k,116322935396671+c.lower,116323325203364+c.upper)) = pointBounds72970 := by
 decide +kernel
def cuts72971 : List PrefixCut := [⟨64,166029380,166029485⟩]
theorem checked72971 : checkPrefixCuts (2^48) 9568387073 10 Manual.Count131072.C072971.packed 64 cuts72971 = true := by
 decide +kernel
def cuts72972 : List PrefixCut := [⟨51,132845402,132845484⟩,
⟨64,166556605,166556706⟩]
theorem checked72972 : checkPrefixCuts (2^48) 9568518145 10 Manual.Count131072.C072972.packed 64 cuts72972 = true := by
 decide +kernel
def pointBounds72972 : List (Nat × Nat × Nat) := [(9568622592,116323401568056,116323791375032)]
theorem point_links_checked72972 : (cuts72972.take 1).map (fun c => (9568518145-1+2*2^10*c.k,116323268722654+c.lower,116323658529548+c.upper)) = pointBounds72972 := by
 decide +kernel
def cuts72973 : List PrefixCut := [⟨64,169966598,169966700⟩]
theorem checked72973 : checkPrefixCuts (2^48) 9568649217 10 Manual.Count131072.C072973.packed 64 cuts72973 = true := by
 decide +kernel
def cuts72974 : List PrefixCut := [⟨64,166404972,166405074⟩]
theorem checked72974 : checkPrefixCuts (2^48) 9568780289 10 Manual.Count131072.C072974.packed 64 cuts72974 = true := by
 decide +kernel
def cuts72975 : List PrefixCut := [⟨6,15560821,15560831⟩,
⟨64,166343853,166343952⟩]
theorem checked72975 : checkPrefixCuts (2^48) 9568911361 10 Manual.Count131072.C072975.packed 64 cuts72975 = true := by
 decide +kernel
def pointBounds72975 : List (Nat × Nat × Nat) := [(9568923648,116323787211650,116324177018859)]
theorem point_links_checked72975 : (cuts72975.take 1).map (fun c => (9568911361-1+2*2^10*c.k,116323771650829+c.lower,116324161458028+c.upper)) = pointBounds72975 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000092
