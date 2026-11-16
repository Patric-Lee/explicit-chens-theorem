import PlattAssemblyKernel
import PlattCertificates.Count131072.C050928
import PlattCertificates.Count131072.C050929
import PlattCertificates.Count131072.C050930
import PlattCertificates.Count131072.C050931
import PlattCertificates.Count131072.C050932
import PlattCertificates.Count131072.C050933
import PlattCertificates.Count131072.C050934
import PlattCertificates.Count131072.C050935
import PlattCertificates.Count131072.C050936
import PlattCertificates.Count131072.C050937
import PlattCertificates.Count131072.C050938
import PlattCertificates.Count131072.C050939
import PlattCertificates.Count131072.C050940
import PlattCertificates.Count131072.C050941
import PlattCertificates.Count131072.C050942
import PlattCertificates.Count131072.C050943
import PlattCertificates.Count131072.C050944
import PlattCertificates.Count131072.C050945
import PlattCertificates.Count131072.C050946
import PlattCertificates.Count131072.C050947
import PlattCertificates.Count131072.C050948
import PlattCertificates.Count131072.C050949
import PlattCertificates.Count131072.C050950
import PlattCertificates.Count131072.C050951
import PlattCertificates.Count131072.C050952
import PlattCertificates.Count131072.C050953
import PlattCertificates.Count131072.C050954
import PlattCertificates.Count131072.C050955
import PlattCertificates.Count131072.C050956
import PlattCertificates.Count131072.C050957
import PlattCertificates.Count131072.C050958
import PlattCertificates.Count131072.C050959
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000029
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50928 : List PrefixCut := [⟨64,239744719,239744851⟩]
theorem checked50928 : checkPrefixCuts (2^48) 6679166977 10 Manual.Count131072.C050928.packed 64 cuts50928 = true := by
 decide +kernel
def cuts50929 : List PrefixCut := [⟨30,114202633,114202697⟩,
⟨64,243743393,243743530⟩]
theorem checked50929 : checkPrefixCuts (2^48) 6679298049 10 Manual.Count131072.C050929.packed 64 cuts50929 = true := by
 decide +kernel
def pointBounds50929 : List (Nat × Nat × Nat) := [(6679359488,111885999724034,111886386976457)]
theorem point_links_checked50929 : (cuts50929.take 1).map (fun c => (6679298049-1+2*2^10*c.k,111885885521401+c.lower,111886272773760+c.upper)) = pointBounds50929 := by
 decide +kernel
def cuts50930 : List PrefixCut := [⟨64,249933228,249933370⟩]
theorem checked50930 : checkPrefixCuts (2^48) 6679429121 10 Manual.Count131072.C050930.packed 64 cuts50930 = true := by
 decide +kernel
def cuts50931 : List PrefixCut := [⟨4,15465274,15465282⟩,
⟨64,245377283,245377421⟩]
theorem checked50931 : checkPrefixCuts (2^48) 6679560193 10 Manual.Count131072.C050931.packed 64 cuts50931 = true := by
 decide +kernel
def pointBounds50931 : List (Nat × Nat × Nat) := [(6679568384,111886394663296,111886781915942)]
theorem point_links_checked50931 : (cuts50931.take 1).map (fun c => (6679560193-1+2*2^10*c.k,111886379198022+c.lower,111886766450660+c.upper)) = pointBounds50931 := by
 decide +kernel
def cuts50932 : List PrefixCut := [⟨42,162486581,162486673⟩,
⟨64,245372466,245372606⟩]
theorem checked50932 : checkPrefixCuts (2^48) 6679691265 10 Manual.Count131072.C050932.packed 64 cuts50932 = true := by
 decide +kernel
def pointBounds50932 : List (Nat × Nat × Nat) := [(6679777280,111886787061886,111887174314754)]
theorem point_links_checked50932 : (cuts50932.take 1).map (fun c => (6679691265-1+2*2^10*c.k,111886624575305+c.lower,111887011828081+c.upper)) = pointBounds50932 := by
 decide +kernel
def cuts50933 : List PrefixCut := [⟨64,243471445,243471582⟩]
theorem checked50933 : checkPrefixCuts (2^48) 6679822337 10 Manual.Count131072.C050933.packed 64 cuts50933 = true := by
 decide +kernel
def cuts50934 : List PrefixCut := [⟨16,61688791,61688825⟩,
⟨64,245025731,245025871⟩]
theorem checked50934 : checkPrefixCuts (2^48) 6679953409 10 Manual.Count131072.C050934.packed 64 cuts50934 = true := by
 decide +kernel
def pointBounds50934 : List (Nat × Nat × Nat) := [(6679986176,111887175108007,111887562361094)]
theorem point_links_checked50934 : (cuts50934.take 1).map (fun c => (6679953409-1+2*2^10*c.k,111887113419216+c.lower,111887500672269+c.upper)) = pointBounds50934 := by
 decide +kernel
def cuts50935 : List PrefixCut := [⟨54,208025814,208025932⟩,
⟨64,245990049,245990189⟩]
theorem checked50935 : checkPrefixCuts (2^48) 6680084481 10 Manual.Count131072.C050935.packed 64 cuts50935 = true := by
 decide +kernel
def pointBounds50935 : List (Nat × Nat × Nat) := [(6680195072,111887566470761,111887953724072)]
theorem point_links_checked50935 : (cuts50935.take 1).map (fun c => (6680084481-1+2*2^10*c.k,111887358444947+c.lower,111887745698140+c.upper)) = pointBounds50935 := by
 decide +kernel
def cuts50936 : List PrefixCut := [⟨64,241266073,241266211⟩]
theorem checked50936 : checkPrefixCuts (2^48) 6680215553 10 Manual.Count131072.C050936.packed 64 cuts50936 = true := by
 decide +kernel
def cuts50937 : List PrefixCut := [⟨28,106979734,106979796⟩,
⟨64,244758498,244758637⟩]
theorem checked50937 : checkPrefixCuts (2^48) 6680346625 10 Manual.Count131072.C050937.packed 64 cuts50937 = true := by
 decide +kernel
def pointBounds50937 : List (Nat × Nat × Nat) := [(6680403968,111887952680803,111888339934336)]
theorem point_links_checked50937 : (cuts50937.take 1).map (fun c => (6680346625-1+2*2^10*c.k,111887845701069+c.lower,111888232954540+c.upper)) = pointBounds50937 := by
 decide +kernel
def cuts50938 : List PrefixCut := [⟨64,245090783,245090920⟩]
theorem checked50938 : checkPrefixCuts (2^48) 6680477697 10 Manual.Count131072.C050938.packed 64 cuts50938 = true := by
 decide +kernel
def cuts50939 : List PrefixCut := [⟨2,8089557,8089561⟩,
⟨64,245001701,245001843⟩]
theorem checked50939 : checkPrefixCuts (2^48) 6680608769 10 Manual.Count131072.C050939.packed 64 cuts50939 = true := by
 decide +kernel
def pointBounds50939 : List (Nat × Nat × Nat) := [(6680612864,111888343639907,111888730893658)]
theorem point_links_checked50939 : (cuts50939.take 1).map (fun c => (6680608769-1+2*2^10*c.k,111888335550350+c.lower,111888722804097+c.upper)) = pointBounds50939 := by
 decide +kernel
def cuts50940 : List PrefixCut := [⟨40,156436262,156436349⟩,
⟨64,245797430,245797568⟩]
theorem checked50940 : checkPrefixCuts (2^48) 6680739841 10 Manual.Count131072.C050940.packed 64 cuts50940 = true := by
 decide +kernel
def pointBounds50940 : List (Nat × Nat × Nat) := [(6680821760,111888736988313,111889124242289)]
theorem point_links_checked50940 : (cuts50940.take 1).map (fun c => (6680739841-1+2*2^10*c.k,111888580552051+c.lower,111888967805940+c.upper)) = pointBounds50940 := by
 decide +kernel
def cuts50941 : List PrefixCut := [⟨64,247182870,247183014⟩]
theorem checked50941 : checkPrefixCuts (2^48) 6680870913 10 Manual.Count131072.C050941.packed 64 cuts50941 = true := by
 decide +kernel
def cuts50942 : List PrefixCut := [⟨14,53632190,53632222⟩,
⟨64,241448350,241448487⟩]
theorem checked50942 : checkPrefixCuts (2^48) 6681001985 10 Manual.Count131072.C050942.packed 64 cuts50942 = true := by
 decide +kernel
def pointBounds50942 : List (Nat × Nat × Nat) := [(6681030656,111889127164541,111889514418744)]
theorem point_links_checked50942 : (cuts50942.take 1).map (fun c => (6681001985-1+2*2^10*c.k,111889073532351+c.lower,111889460786522+c.upper)) = pointBounds50942 := by
 decide +kernel
def cuts50943 : List PrefixCut := [⟨52,199735865,199735977⟩,
⟨64,245319513,245319652⟩]
theorem checked50943 : checkPrefixCuts (2^48) 6681133057 10 Manual.Count131072.C050943.packed 64 cuts50943 = true := by
 decide +kernel
def pointBounds50943 : List (Nat × Nat × Nat) := [(6681239552,111889514716566,111889901970986)]
theorem point_links_checked50943 : (cuts50943.take 1).map (fun c => (6681133057-1+2*2^10*c.k,111889314980701+c.lower,111889702235009+c.upper)) = pointBounds50943 := by
 decide +kernel
def cuts50944 : List PrefixCut := [⟨64,242112918,242113056⟩]
theorem checked50944 : checkPrefixCuts (2^48) 6681264129 10 Manual.Count131072.C050944.packed 64 cuts50944 = true := by
 decide +kernel
def cuts50945 : List PrefixCut := [⟨26,99211423,99211479⟩,
⟨64,244593709,244593850⟩]
theorem checked50945 : checkPrefixCuts (2^48) 6681395201 10 Manual.Count131072.C050945.packed 64 cuts50945 = true := by
 decide +kernel
def pointBounds50945 : List (Nat × Nat × Nat) := [(6681448448,111889901624555,111890288879196)]
theorem point_links_checked50945 : (cuts50945.take 1).map (fun c => (6681395201-1+2*2^10*c.k,111889802413132+c.lower,111890189667717+c.upper)) = pointBounds50945 := by
 decide +kernel
def cuts50946 : List PrefixCut := [⟨64,243367231,243367369⟩]
theorem checked50946 : checkPrefixCuts (2^48) 6681526273 10 Manual.Count131072.C050946.packed 64 cuts50946 = true := by
 decide +kernel
def pointBounds50946 : List (Nat × Nat × Nat) := [(6681657344,111890290374072,111890677628936)]
theorem point_links_checked50946 : (cuts50946.take 1).map (fun c => (6681526273-1+2*2^10*c.k,111890047006841+c.lower,111890434261567+c.upper)) = pointBounds50946 := by
 decide +kernel
def cuts50947 : List PrefixCut := [⟨64,245005362,245005505⟩]
theorem checked50947 : checkPrefixCuts (2^48) 6681657345 10 Manual.Count131072.C050947.packed 64 cuts50947 = true := by
 decide +kernel
def cuts50948 : List PrefixCut := [⟨38,145248504,145248586⟩,
⟨64,246306439,246306577⟩]
theorem checked50948 : checkPrefixCuts (2^48) 6681788417 10 Manual.Count131072.C050948.packed 64 cuts50948 = true := by
 decide +kernel
def pointBounds50948 : List (Nat × Nat × Nat) := [(6681866240,111890680627938,111891067883027)]
theorem point_links_checked50948 : (cuts50948.take 1).map (fun c => (6681788417-1+2*2^10*c.k,111890535379434+c.lower,111890922634441+c.upper)) = pointBounds50948 := by
 decide +kernel
def cuts50949 : List PrefixCut := [⟨64,243563528,243563662⟩]
theorem checked50949 : checkPrefixCuts (2^48) 6681919489 10 Manual.Count131072.C050949.packed 64 cuts50949 = true := by
 decide +kernel
def cuts50950 : List PrefixCut := [⟨12,46462721,46462747⟩,
⟨64,244190601,244190740⟩]
theorem checked50950 : checkPrefixCuts (2^48) 6682050561 10 Manual.Count131072.C050950.packed 64 cuts50950 = true := by
 decide +kernel
def pointBounds50950 : List (Nat × Nat × Nat) := [(6682075136,111891071712122,111891458967427)]
theorem point_links_checked50950 : (cuts50950.take 1).map (fun c => (6682050561-1+2*2^10*c.k,111891025249401+c.lower,111891412504680+c.upper)) = pointBounds50950 := by
 decide +kernel
def cuts50951 : List PrefixCut := [⟨50,191364239,191364348⟩,
⟨64,244691282,244691423⟩]
theorem checked50951 : checkPrefixCuts (2^48) 6682181633 10 Manual.Count131072.C050951.packed 64 cuts50951 = true := by
 decide +kernel
def pointBounds50951 : List (Nat × Nat × Nat) := [(6682284032,111891460804241,111891848059768)]
theorem point_links_checked50951 : (cuts50951.take 1).map (fun c => (6682181633-1+2*2^10*c.k,111891269440002+c.lower,111891656695420+c.upper)) = pointBounds50951 := by
 decide +kernel
def cuts50952 : List PrefixCut := [⟨64,244897090,244897233⟩]
theorem checked50952 : checkPrefixCuts (2^48) 6682312705 10 Manual.Count131072.C050952.packed 64 cuts50952 = true := by
 decide +kernel
def cuts50953 : List PrefixCut := [⟨24,95278602,95278654⟩,
⟨64,247840806,247840945⟩]
theorem checked50953 : checkPrefixCuts (2^48) 6682443777 10 Manual.Count131072.C050953.packed 64 cuts50953 = true := by
 decide +kernel
def pointBounds50953 : List (Nat × Nat × Nat) := [(6682492928,111891854306976,111892241562730)]
theorem point_links_checked50953 : (cuts50953.take 1).map (fun c => (6682443777-1+2*2^10*c.k,111891759028374+c.lower,111892146284076+c.upper)) = pointBounds50953 := by
 decide +kernel
def cuts50954 : List PrefixCut := [⟨62,236716247,236716382⟩,
⟨64,244339951,244340090⟩]
theorem checked50954 : checkPrefixCuts (2^48) 6682574849 10 Manual.Count131072.C050954.packed 64 cuts50954 = true := by
 decide +kernel
def pointBounds50954 : List (Nat × Nat × Nat) := [(6682701824,111892243585427,111892630841403)]
theorem point_links_checked50954 : (cuts50954.take 1).map (fun c => (6682574849-1+2*2^10*c.k,111892006869180+c.lower,111892394125021+c.upper)) = pointBounds50954 := by
 decide +kernel
def cuts50955 : List PrefixCut := [⟨64,243871812,243871955⟩]
theorem checked50955 : checkPrefixCuts (2^48) 6682705921 10 Manual.Count131072.C050955.packed 64 cuts50955 = true := by
 decide +kernel
def cuts50956 : List PrefixCut := [⟨36,136844110,136844196⟩,
⟨64,244835759,244835910⟩]
theorem checked50956 : checkPrefixCuts (2^48) 6682836993 10 Manual.Count131072.C050956.packed 64 cuts50956 = true := by
 decide +kernel
def pointBounds50956 : List (Nat × Nat × Nat) := [(6682910720,111892631925053,111893019181262)]
theorem point_links_checked50956 : (cuts50956.take 1).map (fun c => (6682836993-1+2*2^10*c.k,111892495080943+c.lower,111892882337066+c.upper)) = pointBounds50956 := by
 decide +kernel
def cuts50957 : List PrefixCut := [⟨64,242682966,242683100⟩]
theorem checked50957 : checkPrefixCuts (2^48) 6682968065 10 Manual.Count131072.C050957.packed 64 cuts50957 = true := by
 decide +kernel
def cuts50958 : List PrefixCut := [⟨10,36599984,36600004⟩,
⟨64,243688988,243689127⟩]
theorem checked50958 : checkPrefixCuts (2^48) 6683099137 10 Manual.Count131072.C050958.packed 64 cuts50958 = true := by
 decide +kernel
def pointBounds50958 : List (Nat × Nat × Nat) := [(6683119616,111893019199652,111893406456080)]
theorem point_links_checked50958 : (cuts50958.take 1).map (fun c => (6683099137-1+2*2^10*c.k,111892982599668+c.lower,111893369856076+c.upper)) = pointBounds50958 := by
 decide +kernel
def cuts50959 : List PrefixCut := [⟨48,184806266,184806372⟩,
⟨64,244821383,244821524⟩]
theorem checked50959 : checkPrefixCuts (2^48) 6683230209 10 Manual.Count131072.C050959.packed 64 cuts50959 = true := by
 decide +kernel
def pointBounds50959 : List (Nat × Nat × Nat) := [(6683328512,111893411094922,111893798351575)]
theorem point_links_checked50959 : (cuts50959.take 1).map (fun c => (6683230209-1+2*2^10*c.k,111893226288656+c.lower,111893613545203+c.upper)) = pointBounds50959 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000029
