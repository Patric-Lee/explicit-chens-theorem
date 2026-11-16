import PlattAssemblyKernel
import PlattCertificates.Count131072.C060928
import PlattCertificates.Count131072.C060929
import PlattCertificates.Count131072.C060930
import PlattCertificates.Count131072.C060931
import PlattCertificates.Count131072.C060932
import PlattCertificates.Count131072.C060933
import PlattCertificates.Count131072.C060934
import PlattCertificates.Count131072.C060935
import PlattCertificates.Count131072.C060936
import PlattCertificates.Count131072.C060937
import PlattCertificates.Count131072.C060938
import PlattCertificates.Count131072.C060939
import PlattCertificates.Count131072.C060940
import PlattCertificates.Count131072.C060941
import PlattCertificates.Count131072.C060942
import PlattCertificates.Count131072.C060943
import PlattCertificates.Count131072.C060944
import PlattCertificates.Count131072.C060945
import PlattCertificates.Count131072.C060946
import PlattCertificates.Count131072.C060947
import PlattCertificates.Count131072.C060948
import PlattCertificates.Count131072.C060949
import PlattCertificates.Count131072.C060950
import PlattCertificates.Count131072.C060951
import PlattCertificates.Count131072.C060952
import PlattCertificates.Count131072.C060953
import PlattCertificates.Count131072.C060954
import PlattCertificates.Count131072.C060955
import PlattCertificates.Count131072.C060956
import PlattCertificates.Count131072.C060957
import PlattCertificates.Count131072.C060958
import PlattCertificates.Count131072.C060959
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000029
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60928 : List PrefixCut := [⟨64,199393913,199394029⟩]
theorem checked60928 : checkPrefixCuts (2^48) 7989886977 10 Manual.Count131072.C060928.packed 64 cuts60928 = true := by
 decide +kernel
def cuts60929 : List PrefixCut := [⟨8,25434819,25434834⟩,
⟨64,202948672,202948789⟩]
theorem checked60929 : checkPrefixCuts (2^48) 7990018049 10 Manual.Count131072.C060929.packed 64 cuts60929 = true := by
 decide +kernel
def pointBounds60929 : List (Nat × Nat × Nat) := [(7990034432,114106482937432,114106871453072)]
theorem point_links_checked60929 : (cuts60929.take 1).map (fun c => (7990018049-1+2*2^10*c.k,114106457502613+c.lower,114106846018238+c.upper)) = pointBounds60929 := by
 decide +kernel
def cuts60930 : List PrefixCut := [⟨64,202170330,202170446⟩]
theorem checked60930 : checkPrefixCuts (2^48) 7990149121 10 Manual.Count131072.C060930.packed 64 cuts60930 = true := by
 decide +kernel
def cuts60931 : List PrefixCut := [⟨2,5636345,5636348⟩,
⟨64,201990886,201991000⟩]
theorem checked60931 : checkPrefixCuts (2^48) 7990280193 10 Manual.Count131072.C060931.packed 64 cuts60931 = true := by
 decide +kernel
def pointBounds60931 : List (Nat × Nat × Nat) := [(7990284288,114106868257960,114107256773821)]
theorem point_links_checked60931 : (cuts60931.take 1).map (fun c => (7990280193-1+2*2^10*c.k,114106862621615+c.lower,114107251137473+c.upper)) = pointBounds60931 := by
 decide +kernel
def cuts60932 : List PrefixCut := [⟨60,193744719,193744831⟩,
⟨64,206109054,206109173⟩]
theorem checked60932 : checkPrefixCuts (2^48) 7990411265 10 Manual.Count131072.C060932.packed 64 cuts60932 = true := by
 decide +kernel
def pointBounds60932 : List (Nat × Nat × Nat) := [(7990534144,114107258357220,114107646873304)]
theorem point_links_checked60932 : (cuts60932.take 1).map (fun c => (7990411265-1+2*2^10*c.k,114107064612501+c.lower,114107453128473+c.upper)) = pointBounds60932 := by
 decide +kernel
def cuts60933 : List PrefixCut := [⟨64,201843361,201843482⟩]
theorem checked60933 : checkPrefixCuts (2^48) 7990542337 10 Manual.Count131072.C060933.packed 64 cuts60933 = true := by
 decide +kernel
def cuts60934 : List PrefixCut := [⟨54,172251158,172251257⟩,
⟨64,203389966,203390082⟩]
theorem checked60934 : checkPrefixCuts (2^48) 7990673409 10 Manual.Count131072.C060934.packed 64 cuts60934 = true := by
 decide +kernel
def pointBounds60934 : List (Nat × Nat × Nat) := [(7990784000,114107644816074,114108033332385)]
theorem point_links_checked60934 : (cuts60934.take 1).map (fun c => (7990673409-1+2*2^10*c.k,114107472564916+c.lower,114107861081128+c.upper)) = pointBounds60934 := by
 decide +kernel
def cuts60935 : List PrefixCut := [⟨64,202083298,202083413⟩]
theorem checked60935 : checkPrefixCuts (2^48) 7990804481 10 Manual.Count131072.C060935.packed 64 cuts60935 = true := by
 decide +kernel
def cuts60936 : List PrefixCut := [⟨48,150124936,150125021⟩,
⟨64,199966567,199966682⟩]
theorem checked60936 : checkPrefixCuts (2^48) 7990935553 10 Manual.Count131072.C060936.packed 64 cuts60936 = true := by
 decide +kernel
def pointBounds60936 : List (Nat × Nat × Nat) := [(7991033856,114108028163116,114108416679644)]
theorem point_links_checked60936 : (cuts60936.take 1).map (fun c => (7990935553-1+2*2^10*c.k,114107878038180+c.lower,114108266554623+c.upper)) = pointBounds60936 := by
 decide +kernel
def cuts60937 : List PrefixCut := [⟨64,205387692,205387801⟩]
theorem checked60937 : checkPrefixCuts (2^48) 7991066625 10 Manual.Count131072.C060937.packed 64 cuts60937 = true := by
 decide +kernel
def cuts60938 : List PrefixCut := [⟨42,132825661,132825735⟩,
⟨64,200699688,200699803⟩]
theorem checked60938 : checkPrefixCuts (2^48) 7991197697 10 Manual.Count131072.C060938.packed 64 cuts60938 = true := by
 decide +kernel
def pointBounds60938 : List (Nat × Nat × Nat) := [(7991283712,114108416218100,114108804734841)]
theorem point_links_checked60938 : (cuts60938.take 1).map (fun c => (7991197697-1+2*2^10*c.k,114108283392439+c.lower,114108671909106+c.upper)) = pointBounds60938 := by
 decide +kernel
def cuts60939 : List PrefixCut := [⟨64,202070059,202070175⟩]
theorem checked60939 : checkPrefixCuts (2^48) 7991328769 10 Manual.Count131072.C060939.packed 64 cuts60939 = true := by
 decide +kernel
def cuts60940 : List PrefixCut := [⟨36,116689824,116689889⟩,
⟨64,206082022,206082137⟩]
theorem checked60940 : checkPrefixCuts (2^48) 7991459841 10 Manual.Count131072.C060940.packed 64 cuts60940 = true := by
 decide +kernel
def pointBounds60940 : List (Nat × Nat × Nat) := [(7991533568,114108802852010,114109191368973)]
theorem point_links_checked60940 : (cuts60940.take 1).map (fun c => (7991459841-1+2*2^10*c.k,114108686162186+c.lower,114109074679084+c.upper)) = pointBounds60940 := by
 decide +kernel
def cuts60941 : List PrefixCut := [⟨64,202380417,202380534⟩]
theorem checked60941 : checkPrefixCuts (2^48) 7991590913 10 Manual.Count131072.C060941.packed 64 cuts60941 = true := by
 decide +kernel
def cuts60942 : List PrefixCut := [⟨30,93053011,93053064⟩,
⟨64,198326731,198326841⟩]
theorem checked60942 : checkPrefixCuts (2^48) 7991721985 10 Manual.Count131072.C060942.packed 64 cuts60942 = true := by
 decide +kernel
def pointBounds60942 : List (Nat × Nat × Nat) := [(7991783424,114109187677636,114109576194819)]
theorem point_links_checked60942 : (cuts60942.take 1).map (fun c => (7991721985-1+2*2^10*c.k,114109094624625+c.lower,114109483141755+c.upper)) = pointBounds60942 := by
 decide +kernel
def cuts60943 : List PrefixCut := [⟨64,202972506,202972619⟩]
theorem checked60943 : checkPrefixCuts (2^48) 7991853057 10 Manual.Count131072.C060943.packed 64 cuts60943 = true := by
 decide +kernel
def cuts60944 : List PrefixCut := [⟨24,74982409,74982453⟩,
⟨64,201173004,201173117⟩]
theorem checked60944 : checkPrefixCuts (2^48) 7991984129 10 Manual.Count131072.C060944.packed 64 cuts60944 = true := by
 decide +kernel
def pointBounds60944 : List (Nat × Nat × Nat) := [(7992033280,114109570906271,114109959423668)]
theorem point_links_checked60944 : (cuts60944.take 1).map (fun c => (7991984129-1+2*2^10*c.k,114109495923862+c.lower,114109884441215+c.upper)) = pointBounds60944 := by
 decide +kernel
def cuts60945 : List PrefixCut := [⟨64,202437587,202437702⟩]
theorem checked60945 : checkPrefixCuts (2^48) 7992115201 10 Manual.Count131072.C060945.packed 64 cuts60945 = true := by
 decide +kernel
def cuts60946 : List PrefixCut := [⟨18,57194707,57194738⟩,
⟨64,202328609,202328723⟩]
theorem checked60946 : checkPrefixCuts (2^48) 7992246273 10 Manual.Count131072.C060946.packed 64 cuts60946 = true := by
 decide +kernel
def pointBounds60946 : List (Nat × Nat × Nat) := [(7992283136,114109956729160,114110345246772)]
theorem point_links_checked60946 : (cuts60946.take 1).map (fun c => (7992246273-1+2*2^10*c.k,114109899534453+c.lower,114110288052034+c.upper)) = pointBounds60946 := by
 decide +kernel
def cuts60947 : List PrefixCut := [⟨64,198697878,198697992⟩]
theorem checked60947 : checkPrefixCuts (2^48) 7992377345 10 Manual.Count131072.C060947.packed 64 cuts60947 = true := by
 decide +kernel
def cuts60948 : List PrefixCut := [⟨12,37893804,37893823⟩,
⟨64,202533267,202533383⟩]
theorem checked60948 : checkPrefixCuts (2^48) 7992508417 10 Manual.Count131072.C060948.packed 64 cuts60948 = true := by
 decide +kernel
def pointBounds60948 : List (Nat × Nat × Nat) := [(7992532992,114110338454744,114110726972572)]
theorem point_links_checked60948 : (cuts60948.take 1).map (fun c => (7992508417-1+2*2^10*c.k,114110300560940+c.lower,114110689078749+c.upper)) = pointBounds60948 := by
 decide +kernel
def cuts60949 : List PrefixCut := [⟨64,204572524,204572639⟩]
theorem checked60949 : checkPrefixCuts (2^48) 7992639489 10 Manual.Count131072.C060949.packed 64 cuts60949 = true := by
 decide +kernel
def cuts60950 : List PrefixCut := [⟨6,18875860,18875872⟩,
⟨64,199251549,199251669⟩]
theorem checked60950 : checkPrefixCuts (2^48) 7992770561 10 Manual.Count131072.C060950.packed 64 cuts60950 = true := by
 decide +kernel
def pointBounds60950 : List (Nat × Nat × Nat) := [(7992782848,114110726542591,114111115060643)]
theorem point_links_checked60950 : (cuts60950.take 1).map (fun c => (7992770561-1+2*2^10*c.k,114110707666731+c.lower,114111096184771+c.upper)) = pointBounds60950 := by
 decide +kernel
def cuts60951 : List PrefixCut := [⟨64,204354495,204354613⟩]
theorem checked60951 : checkPrefixCuts (2^48) 7992901633 10 Manual.Count131072.C060951.packed 64 cuts60951 = true := by
 decide +kernel
def pointBounds60951 : List (Nat × Nat × Nat) := [(7993032704,114111111272775,114111499791053)]
theorem point_links_checked60951 : (cuts60951.take 1).map (fun c => (7992901633-1+2*2^10*c.k,114110906918280+c.lower,114111295436440+c.upper)) = pointBounds60951 := by
 decide +kernel
def cuts60952 : List PrefixCut := [⟨64,199702798,199702914⟩]
theorem checked60952 : checkPrefixCuts (2^48) 7993032705 10 Manual.Count131072.C060952.packed 64 cuts60952 = true := by
 decide +kernel
def cuts60953 : List PrefixCut := [⟨58,185578788,185578896⟩,
⟨64,203784376,203784495⟩]
theorem checked60953 : checkPrefixCuts (2^48) 7993163777 10 Manual.Count131072.C060953.packed 64 cuts60953 = true := by
 decide +kernel
def pointBounds60953 : List (Nat × Nat × Nat) := [(7993282560,114111496554361,114111885072863)]
theorem point_links_checked60953 : (cuts60953.take 1).map (fun c => (7993163777-1+2*2^10*c.k,114111310975573+c.lower,114111699493967+c.upper)) = pointBounds60953 := by
 decide +kernel
def cuts60954 : List PrefixCut := [⟨64,201210441,201210559⟩]
theorem checked60954 : checkPrefixCuts (2^48) 7993294849 10 Manual.Count131072.C060954.packed 64 cuts60954 = true := by
 decide +kernel
def cuts60955 : List PrefixCut := [⟨52,166240877,166240973⟩,
⟨64,203953759,203953876⟩]
theorem checked60955 : checkPrefixCuts (2^48) 7993425921 10 Manual.Count131072.C060955.packed 64 cuts60955 = true := by
 decide +kernel
def pointBounds60955 : List (Nat × Nat × Nat) := [(7993532416,114111882211267,114112270729994)]
theorem point_links_checked60955 : (cuts60955.take 1).map (fun c => (7993425921-1+2*2^10*c.k,114111715970390+c.lower,114112104489021+c.upper)) = pointBounds60955 := by
 decide +kernel
def cuts60956 : List PrefixCut := [⟨64,202471503,202471616⟩]
theorem checked60956 : checkPrefixCuts (2^48) 7993556993 10 Manual.Count131072.C060956.packed 64 cuts60956 = true := by
 decide +kernel
def cuts60957 : List PrefixCut := [⟨46,146270376,146270461⟩,
⟨64,205109040,205109159⟩]
theorem checked60957 : checkPrefixCuts (2^48) 7993688065 10 Manual.Count131072.C060957.packed 64 cuts60957 = true := by
 decide +kernel
def pointBounds60957 : List (Nat × Nat × Nat) := [(7993782272,114112268666028,114112657184974)]
theorem point_links_checked60957 : (cuts60957.take 1).map (fun c => (7993688065-1+2*2^10*c.k,114112122395652+c.lower,114112510914513+c.upper)) = pointBounds60957 := by
 decide +kernel
def cuts60958 : List PrefixCut := [⟨64,203838073,203838190⟩]
theorem checked60958 : checkPrefixCuts (2^48) 7993819137 10 Manual.Count131072.C060958.packed 64 cuts60958 = true := by
 decide +kernel
def cuts60959 : List PrefixCut := [⟨40,126758916,126758991⟩,
⟨64,203588269,203588388⟩]
theorem checked60959 : checkPrefixCuts (2^48) 7993950209 10 Manual.Count131072.C060959.packed 64 cuts60959 = true := by
 decide +kernel
def pointBounds60959 : List (Nat × Nat × Nat) := [(7994032128,114112658101681,114113046620853)]
theorem point_links_checked60959 : (cuts60959.take 1).map (fun c => (7993950209-1+2*2^10*c.k,114112531342765+c.lower,114112919861862+c.upper)) = pointBounds60959 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000029
