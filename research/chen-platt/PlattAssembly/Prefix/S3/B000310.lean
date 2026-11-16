import PlattAssemblyKernel
import PlattCertificates.Count131072.C029920
import PlattCertificates.Count131072.C029921
import PlattCertificates.Count131072.C029922
import PlattCertificates.Count131072.C029923
import PlattCertificates.Count131072.C029924
import PlattCertificates.Count131072.C029925
import PlattCertificates.Count131072.C029926
import PlattCertificates.Count131072.C029927
import PlattCertificates.Count131072.C029928
import PlattCertificates.Count131072.C029929
import PlattCertificates.Count131072.C029930
import PlattCertificates.Count131072.C029931
import PlattCertificates.Count131072.C029932
import PlattCertificates.Count131072.C029933
import PlattCertificates.Count131072.C029934
import PlattCertificates.Count131072.C029935
import PlattCertificates.Count131072.C029936
import PlattCertificates.Count131072.C029937
import PlattCertificates.Count131072.C029938
import PlattCertificates.Count131072.C029939
import PlattCertificates.Count131072.C029940
import PlattCertificates.Count131072.C029941
import PlattCertificates.Count131072.C029942
import PlattCertificates.Count131072.C029943
import PlattCertificates.Count131072.C029944
import PlattCertificates.Count131072.C029945
import PlattCertificates.Count131072.C029946
import PlattCertificates.Count131072.C029947
import PlattCertificates.Count131072.C029948
import PlattCertificates.Count131072.C029949
import PlattCertificates.Count131072.C029950
import PlattCertificates.Count131072.C029951
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000310
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts29920 : List PrefixCut := [⟨13,42304269,42304292⟩,
⟨128,426621383,426621616⟩]
theorem checked29920 : checkPrefixCuts (2^48) 3925606401 9 Manual.Count131072.C029920.packed 128 cuts29920 = true := by
 decide +kernel
def pointBounds29920 : List (Nat × Nat × Nat) := [(3925619712,105194029908515,105194413210793)]
theorem point_links_checked29920 : (cuts29920.take 1).map (fun c => (3925606401-1+2*2^9*c.k,105193987604246+c.lower,105194370906501+c.upper)) = pointBounds29920 := by
 decide +kernel
def cuts29921 : List PrefixCut := [⟨5,15845662,15845671⟩,
⟨125,413988403,413988638⟩,
⟨128,423882660,423882900⟩]
theorem checked29921 : checkPrefixCuts (2^48) 3925737473 9 Manual.Count131072.C029921.packed 128 cuts29921 = true := by
 decide +kernel
def pointBounds29921 : List (Nat × Nat × Nat) := [(3925742592,105194430071291,105194813373788),(3925865472,105194828214032,105195211516755)]
theorem point_links_checked29921 : (cuts29921.take 2).map (fun c => (3925737473-1+2*2^9*c.k,105194414225629+c.lower,105194797528117+c.upper)) = pointBounds29921 := by
 decide +kernel
def cuts29922 : List PrefixCut := [⟨117,389526467,389526685⟩,
⟨128,425374062,425374301⟩]
theorem checked29922 : checkPrefixCuts (2^48) 3925868545 9 Manual.Count131072.C029922.packed 128 cuts29922 = true := by
 decide +kernel
def pointBounds29922 : List (Nat × Nat × Nat) := [(3925988352,105195227634756,105195610937702)]
theorem point_links_checked29922 : (cuts29922.take 1).map (fun c => (3925868545-1+2*2^9*c.k,105194838108289+c.lower,105195221411017+c.upper)) = pointBounds29922 := by
 decide +kernel
def cuts29923 : List PrefixCut := [⟨109,365568036,365568240⟩,
⟨128,428012529,428012771⟩]
theorem checked29923 : checkPrefixCuts (2^48) 3925999617 9 Manual.Count131072.C029923.packed 128 cuts29923 = true := by
 decide +kernel
def pointBounds29923 : List (Nat × Nat × Nat) := [(3926111232,105195629050387,105196012353558)]
theorem point_links_checked29923 : (cuts29923.take 1).map (fun c => (3925999617-1+2*2^9*c.k,105195263482351+c.lower,105195646785318+c.upper)) = pointBounds29923 := by
 decide +kernel
def cuts29924 : List PrefixCut := [⟨101,336162611,336162796⟩,
⟨128,424772139,424772374⟩]
theorem checked29924 : checkPrefixCuts (2^48) 3926130689 9 Manual.Count131072.C029924.packed 128 cuts29924 = true := by
 decide +kernel
def pointBounds29924 : List (Nat × Nat × Nat) := [(3926234112,105196027657491,105196410960885)]
theorem point_links_checked29924 : (cuts29924.take 1).map (fun c => (3926130689-1+2*2^9*c.k,105195691494880+c.lower,105196074798089+c.upper)) = pointBounds29924 := by
 decide +kernel
def cuts29925 : List PrefixCut := [⟨93,307260919,307261094⟩,
⟨128,425833273,425833512⟩]
theorem checked29925 : checkPrefixCuts (2^48) 3926261761 9 Manual.Count131072.C029925.packed 128 cuts29925 = true := by
 decide +kernel
def pointBounds29925 : List (Nat × Nat × Nat) := [(3926356992,105196423527938,105196806831557)]
theorem point_links_checked29925 : (cuts29925.take 1).map (fun c => (3926261761-1+2*2^9*c.k,105196116267019+c.lower,105196499570463+c.upper)) = pointBounds29925 := by
 decide +kernel
def cuts29926 : List PrefixCut := [⟨85,280368306,280368465⟩,
⟨128,420872691,420872931⟩]
theorem checked29926 : checkPrefixCuts (2^48) 3926392833 9 Manual.Count131072.C029926.packed 128 cuts29926 = true := by
 decide +kernel
def pointBounds29926 : List (Nat × Nat × Nat) := [(3926479872,105196822468598,105197205772440)]
theorem point_links_checked29926 : (cuts29926.take 1).map (fun c => (3926392833-1+2*2^9*c.k,105196542100292+c.lower,105196925403975+c.upper)) = pointBounds29926 := by
 decide +kernel
def cuts29927 : List PrefixCut := [⟨77,255054517,255054662⟩,
⟨128,423654359,423654592⟩]
theorem checked29927 : checkPrefixCuts (2^48) 3926523905 9 Manual.Count131072.C029927.packed 128 cuts29927 = true := by
 decide +kernel
def pointBounds29927 : List (Nat × Nat × Nat) := [(3926602752,105197218027500,105197601331568)]
theorem point_links_checked29927 : (cuts29927.take 1).map (fun c => (3926523905-1+2*2^9*c.k,105196962972983+c.lower,105197346276906+c.upper)) = pointBounds29927 := by
 decide +kernel
def cuts29928 : List PrefixCut := [⟨69,232036194,232036323⟩,
⟨128,428801301,428801541⟩]
theorem checked29928 : checkPrefixCuts (2^48) 3926654977 9 Manual.Count131072.C029928.packed 128 cuts29928 = true := by
 decide +kernel
def pointBounds29928 : List (Nat × Nat × Nat) := [(3926725632,105197618663536,105198001967821)]
theorem point_links_checked29928 : (cuts29928.take 1).map (fun c => (3926654977-1+2*2^9*c.k,105197386627342+c.lower,105197769931498+c.upper)) = pointBounds29928 := by
 decide +kernel
def cuts29929 : List PrefixCut := [⟨61,201923019,201923131⟩,
⟨128,424987959,424988195⟩]
theorem checked29929 : checkPrefixCuts (2^48) 3926786049 9 Manual.Count131072.C029929.packed 128 cuts29929 = true := by
 decide +kernel
def pointBounds29929 : List (Nat × Nat × Nat) := [(3926848512,105198017351662,105198400656170)]
theorem point_links_checked29929 : (cuts29929.take 1).map (fun c => (3926786049-1+2*2^9*c.k,105197815428643+c.lower,105198198733039+c.upper)) = pointBounds29929 := by
 decide +kernel
def cuts29930 : List PrefixCut := [⟨53,175539059,175539153⟩,
⟨128,425905569,425905801⟩]
theorem checked29930 : checkPrefixCuts (2^48) 3926917121 9 Manual.Count131072.C029930.packed 128 cuts29930 = true := by
 decide +kernel
def pointBounds29930 : List (Nat × Nat × Nat) := [(3926971392,105198415955661,105198799260387)]
theorem point_links_checked29930 : (cuts29930.take 1).map (fun c => (3926917121-1+2*2^9*c.k,105198240416602+c.lower,105198623721234+c.upper)) = pointBounds29930 := by
 decide +kernel
def cuts29931 : List PrefixCut := [⟨45,148511692,148511776⟩,
⟨128,424744595,424744832⟩]
theorem checked29931 : checkPrefixCuts (2^48) 3927048193 9 Manual.Count131072.C029931.packed 128 cuts29931 = true := by
 decide +kernel
def pointBounds29931 : List (Nat × Nat × Nat) := [(3927094272,105198814833863,105199198138811)]
theorem point_links_checked29931 : (cuts29931.take 1).map (fun c => (3927048193-1+2*2^9*c.k,105198666322171+c.lower,105199049627035+c.upper)) = pointBounds29931 := by
 decide +kernel
def cuts29932 : List PrefixCut := [⟨37,121701102,121701171⟩,
⟨128,421146758,421146996⟩]
theorem checked29932 : checkPrefixCuts (2^48) 3927179265 9 Manual.Count131072.C029932.packed 128 cuts29932 = true := by
 decide +kernel
def pointBounds29932 : List (Nat × Nat × Nat) := [(3927217152,105199212767868,105199596073038)]
theorem point_links_checked29932 : (cuts29932.take 1).map (fun c => (3927179265-1+2*2^9*c.k,105199091066766+c.lower,105199474371867+c.upper)) = pointBounds29932 := by
 decide +kernel
def cuts29933 : List PrefixCut := [⟨29,97687428,97687482⟩,
⟨128,421491121,421491351⟩]
theorem checked29933 : checkPrefixCuts (2^48) 3927310337 9 Manual.Count131072.C029933.packed 128 cuts29933 = true := by
 decide +kernel
def pointBounds29933 : List (Nat × Nat × Nat) := [(3927340032,105199609900952,105199993206345)]
theorem point_links_checked29933 : (cuts29933.take 1).map (fun c => (3927310337-1+2*2^9*c.k,105199512213524+c.lower,105199895518863+c.upper)) = pointBounds29933 := by
 decide +kernel
def cuts29934 : List PrefixCut := [⟨21,69518512,69518552⟩,
⟨128,427783712,427783951⟩]
theorem checked29934 : checkPrefixCuts (2^48) 3927441409 9 Manual.Count131072.C029934.packed 128 cuts29934 = true := by
 decide +kernel
def pointBounds29934 : List (Nat × Nat × Nat) := [(3927462912,105200003223157,105200386528766)]
theorem point_links_checked29934 : (cuts29934.take 1).map (fun c => (3927441409-1+2*2^9*c.k,105199933704645+c.lower,105200317010214+c.upper)) = pointBounds29934 := by
 decide +kernel
def cuts29935 : List PrefixCut := [⟨13,42426427,42426450⟩,
⟨128,426121154,426121399⟩]
theorem checked29935 : checkPrefixCuts (2^48) 3927572481 9 Manual.Count131072.C029935.packed 128 cuts29935 = true := by
 decide +kernel
def pointBounds29935 : List (Nat × Nat × Nat) := [(3927585792,105200403914784,105200787220615)]
theorem point_links_checked29935 : (cuts29935.take 1).map (fun c => (3927572481-1+2*2^9*c.k,105200361488357+c.lower,105200744794165+c.upper)) = pointBounds29935 := by
 decide +kernel
def cuts29936 : List PrefixCut := [⟨5,16626034,16626044⟩,
⟨125,409481374,409481611⟩,
⟨128,419227355,419227598⟩]
theorem checked29936 : checkPrefixCuts (2^48) 3927703553 9 Manual.Count131072.C029936.packed 128 cuts29936 = true := by
 decide +kernel
def pointBounds29936 : List (Nat × Nat × Nat) := [(3927708672,105200804235545,105201187541608),(3927831552,105201197090885,105201580397175)]
theorem point_links_checked29936 : (cuts29936.take 2).map (fun c => (3927703553-1+2*2^9*c.k,105200787609511+c.lower,105201170915564+c.upper)) = pointBounds29936 := by
 decide +kernel
def cuts29937 : List PrefixCut := [⟨117,385175245,385175462⟩,
⟨128,420646603,420646840⟩]
theorem checked29937 : checkPrefixCuts (2^48) 3927834625 9 Manual.Count131072.C029937.packed 128 cuts29937 = true := by
 decide +kernel
def pointBounds29937 : List (Nat × Nat × Nat) := [(3927954432,105201592012111,105201975318624)]
theorem point_links_checked29937 : (cuts29937.take 1).map (fun c => (3927834625-1+2*2^9*c.k,105201206836866+c.lower,105201590143162+c.upper)) = pointBounds29937 := by
 decide +kernel
def cuts29938 : List PrefixCut := [⟨109,362590397,362590604⟩,
⟨128,426365115,426365359⟩]
theorem checked29938 : checkPrefixCuts (2^48) 3927965697 9 Manual.Count131072.C029938.packed 128 cuts29938 = true := by
 decide +kernel
def pointBounds29938 : List (Nat × Nat × Nat) := [(3928077312,105201990073866,105202373380606)]
theorem point_links_checked29938 : (cuts29938.take 1).map (fun c => (3927965697-1+2*2^9*c.k,105201627483469+c.lower,105202010790002+c.upper)) = pointBounds29938 := by
 decide +kernel
def cuts29939 : List PrefixCut := [⟨101,341655193,341655379⟩,
⟨128,432871589,432871828⟩]
theorem checked29939 : checkPrefixCuts (2^48) 3928096769 9 Manual.Count131072.C029939.packed 128 cuts29939 = true := by
 decide +kernel
def pointBounds29939 : List (Nat × Nat × Nat) := [(3928200192,105202395503777,105202778810740)]
theorem point_links_checked29939 : (cuts29939.take 1).map (fun c => (3928096769-1+2*2^9*c.k,105202053848584+c.lower,105202437155361+c.upper)) = pointBounds29939 := by
 decide +kernel
def cuts29940 : List PrefixCut := [⟨93,307107155,307107323⟩,
⟨128,425691819,425692052⟩]
theorem checked29940 : checkPrefixCuts (2^48) 3928227841 9 Manual.Count131072.C029940.packed 128 cuts29940 = true := by
 decide +kernel
def pointBounds29940 : List (Nat × Nat × Nat) := [(3928323072,105202793827328,105203177134512)]
theorem point_links_checked29940 : (cuts29940.take 1).map (fun c => (3928227841-1+2*2^9*c.k,105202486720173+c.lower,105202870027189+c.upper)) = pointBounds29940 := by
 decide +kernel
def cuts29941 : List PrefixCut := [⟨85,279511485,279511637⟩,
⟨128,421593523,421593757⟩]
theorem checked29941 : checkPrefixCuts (2^48) 3928358913 9 Manual.Count131072.C029941.packed 128 cuts29941 = true := by
 decide +kernel
def pointBounds29941 : List (Nat × Nat × Nat) := [(3928445952,105203191923477,105203575230878)]
theorem point_links_checked29941 : (cuts29941.take 1).map (fun c => (3928358913-1+2*2^9*c.k,105202912411992+c.lower,105203295719241+c.upper)) = pointBounds29941 := by
 decide +kernel
def cuts29942 : List PrefixCut := [⟨77,255571718,255571861⟩,
⟨128,424588715,424588954⟩]
theorem checked29942 : checkPrefixCuts (2^48) 3928489985 9 Manual.Count131072.C029942.packed 128 cuts29942 = true := by
 decide +kernel
def pointBounds29942 : List (Nat × Nat × Nat) := [(3928568832,105203589577233,105203972884859)]
theorem point_links_checked29942 : (cuts29942.take 1).map (fun c => (3928489985-1+2*2^9*c.k,105203334005515+c.lower,105203717312998+c.upper)) = pointBounds29942 := by
 decide +kernel
def cuts29943 : List PrefixCut := [⟨69,233209708,233209838⟩,
⟨128,426580676,426580919⟩]
theorem checked29943 : checkPrefixCuts (2^48) 3928621057 9 Manual.Count131072.C029943.packed 128 cuts29943 = true := by
 decide +kernel
def pointBounds29943 : List (Nat × Nat × Nat) := [(3928691712,105203991803938,105204375111790)]
theorem point_links_checked29943 : (cuts29943.take 1).map (fun c => (3928621057-1+2*2^9*c.k,105203758594230+c.lower,105204141901952+c.upper)) = pointBounds29943 := by
 decide +kernel
def cuts29944 : List PrefixCut := [⟨61,199027842,199027953⟩,
⟨128,420691585,420691818⟩]
theorem checked29944 : checkPrefixCuts (2^48) 3928752129 9 Manual.Count131072.C029944.packed 128 cuts29944 = true := by
 decide +kernel
def pointBounds29944 : List (Nat × Nat × Nat) := [(3928814592,105204384202748,105204767510824)]
theorem point_links_checked29944 : (cuts29944.take 1).map (fun c => (3928752129-1+2*2^9*c.k,105204185174906+c.lower,105204568482871+c.upper)) = pointBounds29944 := by
 decide +kernel
def cuts29945 : List PrefixCut := [⟨53,176740767,176740868⟩,
⟨128,426695430,426695671⟩]
theorem checked29945 : checkPrefixCuts (2^48) 3928883201 9 Manual.Count131072.C029945.packed 128 cuts29945 = true := by
 decide +kernel
def pointBounds29945 : List (Nat × Nat × Nat) := [(3928937472,105204782607258,105205165915557)]
theorem point_links_checked29945 : (cuts29945.take 1).map (fun c => (3928883201-1+2*2^9*c.k,105204605866491+c.lower,105204989174689+c.upper)) = pointBounds29945 := by
 decide +kernel
def cuts29946 : List PrefixCut := [⟨45,148365743,148365828⟩,
⟨128,422454503,422454740⟩]
theorem checked29946 : checkPrefixCuts (2^48) 3929014273 9 Manual.Count131072.C029946.packed 128 cuts29946 = true := by
 decide +kernel
def pointBounds29946 : List (Nat × Nat × Nat) := [(3929060352,105205180927664,105205564236188)]
theorem point_links_checked29946 : (cuts29946.take 1).map (fun c => (3929014273-1+2*2^9*c.k,105205032561921+c.lower,105205415870360+c.upper)) = pointBounds29946 := by
 decide +kernel
def cuts29947 : List PrefixCut := [⟨37,123789341,123789412⟩,
⟨128,423873178,423873418⟩]
theorem checked29947 : checkPrefixCuts (2^48) 3929145345 9 Manual.Count131072.C029947.packed 128 cuts29947 = true := by
 decide +kernel
def pointBounds29947 : List (Nat × Nat × Nat) := [(3929183232,105205578805765,105205962114512)]
theorem point_links_checked29947 : (cuts29947.take 1).map (fun c => (3929145345-1+2*2^9*c.k,105205455016424+c.lower,105205838325100+c.upper)) = pointBounds29947 := by
 decide +kernel
def cuts29948 : List PrefixCut := [⟨29,99859223,99859280⟩,
⟨128,429088367,429088606⟩]
theorem checked29948 : checkPrefixCuts (2^48) 3929276417 9 Manual.Count131072.C029948.packed 128 cuts29948 = true := by
 decide +kernel
def pointBounds29948 : List (Nat × Nat × Nat) := [(3929306112,105205978748825,105206362057798)]
theorem point_links_checked29948 : (cuts29948.take 1).map (fun c => (3929276417-1+2*2^9*c.k,105205878889602+c.lower,105206262198518+c.upper)) = pointBounds29948 := by
 decide +kernel
def cuts29949 : List PrefixCut := [⟨21,71202915,71202952⟩,
⟨128,430076808,430077043⟩]
theorem checked29949 : checkPrefixCuts (2^48) 3929407489 9 Manual.Count131072.C029949.packed 128 cuts29949 = true := by
 decide +kernel
def pointBounds29949 : List (Nat × Nat × Nat) := [(3929428992,105206379180884,105206762490076)]
theorem point_links_checked29949 : (cuts29949.take 1).map (fun c => (3929407489-1+2*2^9*c.k,105206307977969+c.lower,105206691287124+c.upper)) = pointBounds29949 := by
 decide +kernel
def cuts29950 : List PrefixCut := [⟨13,42906610,42906636⟩,
⟨128,418172047,418172285⟩]
theorem checked29950 : checkPrefixCuts (2^48) 3929538561 9 Manual.Count131072.C029950.packed 128 cuts29950 = true := by
 decide +kernel
def pointBounds29950 : List (Nat × Nat × Nat) := [(3929551872,105206780961387,105207164270803)]
theorem point_links_checked29950 : (cuts29950.take 1).map (fun c => (3929538561-1+2*2^9*c.k,105206738054777+c.lower,105207121364167+c.upper)) = pointBounds29950 := by
 decide +kernel
def cuts29951 : List PrefixCut := [⟨5,16760973,16760983⟩,
⟨125,418874529,418874764⟩,
⟨128,428472383,428472624⟩]
theorem checked29951 : checkPrefixCuts (2^48) 3929669633 9 Manual.Count131072.C029951.packed 128 cuts29951 = true := by
 decide +kernel
def pointBounds29951 : List (Nat × Nat × Nat) := [(3929674752,105207172987797,105207556297435),(3929797632,105207575101353,105207958411216)]
theorem point_links_checked29951 : (cuts29951.take 2).map (fun c => (3929669633-1+2*2^9*c.k,105207156226824+c.lower,105207539536452+c.upper)) = pointBounds29951 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000310
