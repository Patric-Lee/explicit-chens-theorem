import PlattAssemblyKernel
import PlattCertificates.Count131072.C062912
import PlattCertificates.Count131072.C062913
import PlattCertificates.Count131072.C062914
import PlattCertificates.Count131072.C062915
import PlattCertificates.Count131072.C062916
import PlattCertificates.Count131072.C062917
import PlattCertificates.Count131072.C062918
import PlattCertificates.Count131072.C062919
import PlattCertificates.Count131072.C062920
import PlattCertificates.Count131072.C062921
import PlattCertificates.Count131072.C062922
import PlattCertificates.Count131072.C062923
import PlattCertificates.Count131072.C062924
import PlattCertificates.Count131072.C062925
import PlattCertificates.Count131072.C062926
import PlattCertificates.Count131072.C062927
import PlattCertificates.Count131072.C062928
import PlattCertificates.Count131072.C062929
import PlattCertificates.Count131072.C062930
import PlattCertificates.Count131072.C062931
import PlattCertificates.Count131072.C062932
import PlattCertificates.Count131072.C062933
import PlattCertificates.Count131072.C062934
import PlattCertificates.Count131072.C062935
import PlattCertificates.Count131072.C062936
import PlattCertificates.Count131072.C062937
import PlattCertificates.Count131072.C062938
import PlattCertificates.Count131072.C062939
import PlattCertificates.Count131072.C062940
import PlattCertificates.Count131072.C062941
import PlattCertificates.Count131072.C062942
import PlattCertificates.Count131072.C062943
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000091
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts62912 : List PrefixCut := [⟨64,195258281,195258392⟩]
theorem checked62912 : checkPrefixCuts (2^48) 8249933825 10 Manual.Count131072.C062912.packed 64 cuts62912 = true := by
 decide +kernel
def cuts62913 : List PrefixCut := [⟨38,118252087,118252155⟩,
⟨64,197916376,197916488⟩]
theorem checked62913 : checkPrefixCuts (2^48) 8250064897 10 Manual.Count131072.C062913.packed 64 cuts62913 = true := by
 decide +kernel
def pointBounds62913 : List (Nat × Nat × Nat) := [(8250142720,114501701014327,114502089756763)]
theorem point_links_checked62913 : (cuts62913.take 1).map (fun c => (8250064897-1+2*2^10*c.k,114501582762240+c.lower,114501971504608+c.upper)) = pointBounds62913 := by
 decide +kernel
def cuts62914 : List PrefixCut := [⟨64,196821483,196821596⟩]
theorem checked62914 : checkPrefixCuts (2^48) 8250195969 10 Manual.Count131072.C062914.packed 64 cuts62914 = true := by
 decide +kernel
def cuts62915 : List PrefixCut := [⟨36,111356790,111356852⟩,
⟨64,197466569,197466681⟩]
theorem checked62915 : checkPrefixCuts (2^48) 8250327041 10 Manual.Count131072.C062915.packed 64 cuts62915 = true := by
 decide +kernel
def pointBounds62915 : List (Nat × Nat × Nat) := [(8250400768,114502088856889,114502477599544)]
theorem point_links_checked62915 : (cuts62915.take 1).map (fun c => (8250327041-1+2*2^10*c.k,114501977500099+c.lower,114502366242692+c.upper)) = pointBounds62915 := by
 decide +kernel
def cuts62916 : List PrefixCut := [⟨64,195587050,195587159⟩]
theorem checked62916 : checkPrefixCuts (2^48) 8250458113 10 Manual.Count131072.C062916.packed 64 cuts62916 = true := by
 decide +kernel
def cuts62917 : List PrefixCut := [⟨34,104257236,104257298⟩,
⟨64,197323820,197323932⟩]
theorem checked62917 : checkPrefixCuts (2^48) 8250589185 10 Manual.Count131072.C062917.packed 64 cuts62917 = true := by
 decide +kernel
def pointBounds62917 : List (Nat × Nat × Nat) := [(8250658816,114502474810954,114502863553830)]
theorem point_links_checked62917 : (cuts62917.take 1).map (fun c => (8250589185-1+2*2^10*c.k,114502370553718+c.lower,114502759296532+c.upper)) = pointBounds62917 := by
 decide +kernel
def cuts62918 : List PrefixCut := [⟨64,194455052,194455169⟩]
theorem checked62918 : checkPrefixCuts (2^48) 8250720257 10 Manual.Count131072.C062918.packed 64 cuts62918 = true := by
 decide +kernel
def cuts62919 : List PrefixCut := [⟨32,98522707,98522765⟩,
⟨64,196805843,196805956⟩]
theorem checked62919 : checkPrefixCuts (2^48) 8250851329 10 Manual.Count131072.C062919.packed 64 cuts62919 = true := by
 decide +kernel
def pointBounds62919 : List (Nat × Nat × Nat) := [(8250916864,114502860855297,114503249598398)]
theorem point_links_checked62919 : (cuts62919.take 1).map (fun c => (8250851329-1+2*2^10*c.k,114502762332590+c.lower,114503151075633+c.upper)) = pointBounds62919 := by
 decide +kernel
def cuts62920 : List PrefixCut := [⟨64,195813424,195813535⟩]
theorem checked62920 : checkPrefixCuts (2^48) 8250982401 10 Manual.Count131072.C062920.packed 64 cuts62920 = true := by
 decide +kernel
def cuts62921 : List PrefixCut := [⟨30,93811953,93812008⟩,
⟨64,199016962,199017078⟩]
theorem checked62921 : checkPrefixCuts (2^48) 8251113473 10 Manual.Count131072.C062921.packed 64 cuts62921 = true := by
 decide +kernel
def pointBounds62921 : List (Nat × Nat × Nat) := [(8251174912,114503248763810,114503637507132)]
theorem point_links_checked62921 : (cuts62921.take 1).map (fun c => (8251113473-1+2*2^10*c.k,114503154951857+c.lower,114503543695124+c.upper)) = pointBounds62921 := by
 decide +kernel
def cuts62922 : List PrefixCut := [⟨64,195773086,195773196⟩]
theorem checked62922 : checkPrefixCuts (2^48) 8251244545 10 Manual.Count131072.C062922.packed 64 cuts62922 = true := by
 decide +kernel
def cuts62923 : List PrefixCut := [⟨28,85622024,85622077⟩,
⟨64,196929778,196929892⟩]
theorem checked62923 : checkPrefixCuts (2^48) 8251375617 10 Manual.Count131072.C062923.packed 64 cuts62923 = true := by
 decide +kernel
def pointBounds62923 : List (Nat × Nat × Nat) := [(8251432960,114503635363929,114504024107475)]
theorem point_links_checked62923 : (cuts62923.take 1).map (fun c => (8251375617-1+2*2^10*c.k,114503549741905+c.lower,114503938485398+c.upper)) = pointBounds62923 := by
 decide +kernel
def cuts62924 : List PrefixCut := [⟨64,196517309,196517423⟩]
theorem checked62924 : checkPrefixCuts (2^48) 8251506689 10 Manual.Count131072.C062924.packed 64 cuts62924 = true := by
 decide +kernel
def cuts62925 : List PrefixCut := [⟨26,80570862,80570905⟩,
⟨64,197708093,197708205⟩]
theorem checked62925 : checkPrefixCuts (2^48) 8251637761 10 Manual.Count131072.C062925.packed 64 cuts62925 = true := by
 decide +kernel
def pointBounds62925 : List (Nat × Nat × Nat) := [(8251691008,114504023759854,114504412503618)]
theorem point_links_checked62925 : (cuts62925.take 1).map (fun c => (8251637761-1+2*2^10*c.k,114503943188992+c.lower,114504331932713+c.upper)) = pointBounds62925 := by
 decide +kernel
def cuts62926 : List PrefixCut := [⟨64,194669116,194669225⟩]
theorem checked62926 : checkPrefixCuts (2^48) 8251768833 10 Manual.Count131072.C062926.packed 64 cuts62926 = true := by
 decide +kernel
def cuts62927 : List PrefixCut := [⟨24,74530817,74530860⟩,
⟨64,196883184,196883296⟩]
theorem checked62927 : checkPrefixCuts (2^48) 8251899905 10 Manual.Count131072.C062927.packed 64 cuts62927 = true := by
 decide +kernel
def pointBounds62927 : List (Nat × Nat × Nat) := [(8251949056,114504410097018,114504798841003)]
theorem point_links_checked62927 : (cuts62927.take 1).map (fun c => (8251899905-1+2*2^10*c.k,114504335566201+c.lower,114504724310143+c.upper)) = pointBounds62927 := by
 decide +kernel
def cuts62928 : List PrefixCut := [⟨64,194185380,194185495⟩]
theorem checked62928 : checkPrefixCuts (2^48) 8252030977 10 Manual.Count131072.C062928.packed 64 cuts62928 = true := by
 decide +kernel
def cuts62929 : List PrefixCut := [⟨22,67570200,67570239⟩,
⟨64,197593208,197593316⟩]
theorem checked62929 : checkPrefixCuts (2^48) 8252162049 10 Manual.Count131072.C062929.packed 64 cuts62929 = true := by
 decide +kernel
def pointBounds62929 : List (Nat × Nat × Nat) := [(8252207104,114504794204965,114505182949173)]
theorem point_links_checked62929 : (cuts62929.take 1).map (fun c => (8252162049-1+2*2^10*c.k,114504726634765+c.lower,114505115378934+c.upper)) = pointBounds62929 := by
 decide +kernel
def cuts62930 : List PrefixCut := [⟨64,196089303,196089419⟩]
theorem checked62930 : checkPrefixCuts (2^48) 8252293121 10 Manual.Count131072.C062930.packed 64 cuts62930 = true := by
 decide +kernel
def cuts62931 : List PrefixCut := [⟨20,59723217,59723253⟩,
⟨64,193630404,193630515⟩]
theorem checked62931 : checkPrefixCuts (2^48) 8252424193 10 Manual.Count131072.C062931.packed 64 cuts62931 = true := by
 decide +kernel
def pointBounds62931 : List (Nat × Nat × Nat) := [(8252465152,114505180040493,114505568784922)]
theorem point_links_checked62931 : (cuts62931.take 1).map (fun c => (8252424193-1+2*2^10*c.k,114505120317276+c.lower,114505509061669+c.upper)) = pointBounds62931 := by
 decide +kernel
def cuts62932 : List PrefixCut := [⟨64,194104823,194104936⟩]
theorem checked62932 : checkPrefixCuts (2^48) 8252555265 10 Manual.Count131072.C062932.packed 64 cuts62932 = true := by
 decide +kernel
def cuts62933 : List PrefixCut := [⟨18,55492068,55492100⟩,
⟨64,196625660,196625778⟩]
theorem checked62933 : checkPrefixCuts (2^48) 8252686337 10 Manual.Count131072.C062933.packed 64 cuts62933 = true := by
 decide +kernel
def pointBounds62933 : List (Nat × Nat × Nat) := [(8252723200,114505563544571,114505952289220)]
theorem point_links_checked62933 : (cuts62933.take 1).map (fun c => (8252686337-1+2*2^10*c.k,114505508052503+c.lower,114505896797120+c.upper)) = pointBounds62933 := by
 decide +kernel
def cuts62934 : List PrefixCut := [⟨64,197816255,197816370⟩]
theorem checked62934 : checkPrefixCuts (2^48) 8252817409 10 Manual.Count131072.C062934.packed 64 cuts62934 = true := by
 decide +kernel
def cuts62935 : List PrefixCut := [⟨16,48703241,48703269⟩,
⟨64,195596241,195596351⟩]
theorem checked62935 : checkPrefixCuts (2^48) 8252948481 10 Manual.Count131072.C062935.packed 64 cuts62935 = true := by
 decide +kernel
def pointBounds62935 : List (Nat × Nat × Nat) := [(8252981248,114505951197659,114506339942537)]
theorem point_links_checked62935 : (cuts62935.take 1).map (fun c => (8252948481-1+2*2^10*c.k,114505902494418+c.lower,114506291239268+c.upper)) = pointBounds62935 := by
 decide +kernel
def cuts62936 : List PrefixCut := [⟨64,192967039,192967155⟩]
theorem checked62936 : checkPrefixCuts (2^48) 8253079553 10 Manual.Count131072.C062936.packed 64 cuts62936 = true := by
 decide +kernel
def cuts62937 : List PrefixCut := [⟨14,43176725,43176750⟩,
⟨64,196408547,196408662⟩]
theorem checked62937 : checkPrefixCuts (2^48) 8253210625 10 Manual.Count131072.C062937.packed 64 cuts62937 = true := by
 decide +kernel
def pointBounds62937 : List (Nat × Nat × Nat) := [(8253239296,114506334234423,114506722979524)]
theorem point_links_checked62937 : (cuts62937.take 1).map (fun c => (8253210625-1+2*2^10*c.k,114506291057698+c.lower,114506679802774+c.upper)) = pointBounds62937 := by
 decide +kernel
def cuts62938 : List PrefixCut := [⟨64,196303118,196303233⟩]
theorem checked62938 : checkPrefixCuts (2^48) 8253341697 10 Manual.Count131072.C062938.packed 64 cuts62938 = true := by
 decide +kernel
def cuts62939 : List PrefixCut := [⟨12,36525129,36525152⟩,
⟨64,194935856,194935971⟩]
theorem checked62939 : checkPrefixCuts (2^48) 8253472769 10 Manual.Count131072.C062939.packed 64 cuts62939 = true := by
 decide +kernel
def pointBounds62939 : List (Nat × Nat × Nat) := [(8253497344,114506720294492,114507109039821)]
theorem point_links_checked62939 : (cuts62939.take 1).map (fun c => (8253472769-1+2*2^10*c.k,114506683769363+c.lower,114507072514669+c.upper)) = pointBounds62939 := by
 decide +kernel
def cuts62940 : List PrefixCut := [⟨64,196706109,196706227⟩]
theorem checked62940 : checkPrefixCuts (2^48) 8253603841 10 Manual.Count131072.C062940.packed 64 cuts62940 = true := by
 decide +kernel
def cuts62941 : List PrefixCut := [⟨10,30146777,30146795⟩,
⟨64,197248617,197248729⟩]
theorem checked62941 : checkPrefixCuts (2^48) 8253734913 10 Manual.Count131072.C062941.packed 64 cuts62941 = true := by
 decide +kernel
def pointBounds62941 : List (Nat × Nat × Nat) := [(8253755392,114507105558105,114507494303662)]
theorem point_links_checked62941 : (cuts62941.take 1).map (fun c => (8253734913-1+2*2^10*c.k,114507075411328+c.lower,114507464156867+c.upper)) = pointBounds62941 := by
 decide +kernel
def cuts62942 : List PrefixCut := [⟨64,192709931,192710046⟩]
theorem checked62942 : checkPrefixCuts (2^48) 8253865985 10 Manual.Count131072.C062942.packed 64 cuts62942 = true := by
 decide +kernel
def cuts62943 : List PrefixCut := [⟨8,24996483,24996497⟩,
⟨64,196219326,196219438⟩]
theorem checked62943 : checkPrefixCuts (2^48) 8253997057 10 Manual.Count131072.C062943.packed 64 cuts62943 = true := by
 decide +kernel
def pointBounds62943 : List (Nat × Nat × Nat) := [(8254013440,114507490366359,114507879112139)]
theorem point_links_checked62943 : (cuts62943.take 1).map (fun c => (8253997057-1+2*2^10*c.k,114507465369876+c.lower,114507854115642+c.upper)) = pointBounds62943 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000091
