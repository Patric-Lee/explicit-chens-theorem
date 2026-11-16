import PlattAssemblyKernel
import PlattCertificates.Count131072.C048928
import PlattCertificates.Count131072.C048929
import PlattCertificates.Count131072.C048930
import PlattCertificates.Count131072.C048931
import PlattCertificates.Count131072.C048932
import PlattCertificates.Count131072.C048933
import PlattCertificates.Count131072.C048934
import PlattCertificates.Count131072.C048935
import PlattCertificates.Count131072.C048936
import PlattCertificates.Count131072.C048937
import PlattCertificates.Count131072.C048938
import PlattCertificates.Count131072.C048939
import PlattCertificates.Count131072.C048940
import PlattCertificates.Count131072.C048941
import PlattCertificates.Count131072.C048942
import PlattCertificates.Count131072.C048943
import PlattCertificates.Count131072.C048944
import PlattCertificates.Count131072.C048945
import PlattCertificates.Count131072.C048946
import PlattCertificates.Count131072.C048947
import PlattCertificates.Count131072.C048948
import PlattCertificates.Count131072.C048949
import PlattCertificates.Count131072.C048950
import PlattCertificates.Count131072.C048951
import PlattCertificates.Count131072.C048952
import PlattCertificates.Count131072.C048953
import PlattCertificates.Count131072.C048954
import PlattCertificates.Count131072.C048955
import PlattCertificates.Count131072.C048956
import PlattCertificates.Count131072.C048957
import PlattCertificates.Count131072.C048958
import PlattCertificates.Count131072.C048959
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000279
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48928 : List PrefixCut := [⟨64,257214579,257214725⟩]
theorem checked48928 : checkPrefixCuts (2^48) 6417022977 10 Manual.Count131072.C048928.packed 64 cuts48928 = true := by
 decide +kernel
def cuts48929 : List PrefixCut := [⟨16,63688749,63688784⟩,
⟨64,254577583,254577722⟩]
theorem checked48929 : checkPrefixCuts (2^48) 6417154049 10 Manual.Count131072.C048929.packed 64 cuts48929 = true := by
 decide +kernel
def pointBounds48929 : List (Nat × Nat × Nat) := [(6417186816,111387311877680,111387698846135)]
theorem point_links_checked48929 : (cuts48929.take 1).map (fun c => (6417154049-1+2*2^10*c.k,111387248188931+c.lower,111387635157351+c.upper)) = pointBounds48929 := by
 decide +kernel
def cuts48930 : List PrefixCut := [⟨50,196324711,196324820⟩,
⟨64,251019616,251019758⟩]
theorem checked48930 : checkPrefixCuts (2^48) 6417285121 10 Manual.Count131072.C048930.packed 64 cuts48930 = true := by
 decide +kernel
def pointBounds48930 : List (Nat × Nat × Nat) := [(6417387520,111387699091225,111388086059893)]
theorem point_links_checked48930 : (cuts48930.take 1).map (fun c => (6417285121-1+2*2^10*c.k,111387502766514+c.lower,111387889735073+c.upper)) = pointBounds48930 := by
 decide +kernel
def cuts48931 : List PrefixCut := [⟨64,252198732,252198873⟩]
theorem checked48931 : checkPrefixCuts (2^48) 6417416193 10 Manual.Count131072.C048931.packed 64 cuts48931 = true := by
 decide +kernel
def cuts48932 : List PrefixCut := [⟨20,78290204,78290249⟩,
⟨64,254167255,254167397⟩]
theorem checked48932 : checkPrefixCuts (2^48) 6417547265 10 Manual.Count131072.C048932.packed 64 cuts48932 = true := by
 decide +kernel
def pointBounds48932 : List (Nat × Nat × Nat) := [(6417588224,111388084275066,111388471243953)]
theorem point_links_checked48932 : (cuts48932.take 1).map (fun c => (6417547265-1+2*2^10*c.k,111388005984862+c.lower,111388392953704+c.upper)) = pointBounds48932 := by
 decide +kernel
def cuts48933 : List PrefixCut := [⟨54,214733287,214733413⟩,
⟨64,254776077,254776225⟩]
theorem checked48933 : checkPrefixCuts (2^48) 6417678337 10 Manual.Count131072.C048933.packed 64 cuts48933 = true := by
 decide +kernel
def pointBounds48933 : List (Nat × Nat × Nat) := [(6417788928,111388474885404,111388861854514)]
theorem point_links_checked48933 : (cuts48933.take 1).map (fun c => (6417678337-1+2*2^10*c.k,111388260152117+c.lower,111388647121101+c.upper)) = pointBounds48933 := by
 decide +kernel
def cuts48934 : List PrefixCut := [⟨64,256086628,256086772⟩]
theorem checked48934 : checkPrefixCuts (2^48) 6417809409 10 Manual.Count131072.C048934.packed 64 cuts48934 = true := by
 decide +kernel
def cuts48935 : List PrefixCut := [⟨24,93547715,93547768⟩,
⟨64,252353536,252353676⟩]
theorem checked48935 : checkPrefixCuts (2^48) 6417940481 10 Manual.Count131072.C048935.packed 64 cuts48935 = true := by
 decide +kernel
def pointBounds48935 : List (Nat × Nat × Nat) := [(6417989632,111388864562537,111389251531866)]
theorem point_links_checked48935 : (cuts48935.take 1).map (fun c => (6417940481-1+2*2^10*c.k,111388771014822+c.lower,111389157984098+c.upper)) = pointBounds48935 := by
 decide +kernel
def cuts48936 : List PrefixCut := [⟨58,234104448,234104579⟩,
⟨64,257874270,257874415⟩]
theorem checked48936 : checkPrefixCuts (2^48) 6418071553 10 Manual.Count131072.C048936.packed 64 cuts48936 = true := by
 decide +kernel
def pointBounds48936 : List (Nat × Nat × Nat) := [(6418190336,111389257472806,111389644442353)]
theorem point_links_checked48936 : (cuts48936.take 1).map (fun c => (6418071553-1+2*2^10*c.k,111389023368358+c.lower,111389410337774+c.upper)) = pointBounds48936 := by
 decide +kernel
def cuts48937 : List PrefixCut := [⟨64,256027090,256027233⟩]
theorem checked48937 : checkPrefixCuts (2^48) 6418202625 10 Manual.Count131072.C048937.packed 64 cuts48937 = true := by
 decide +kernel
def cuts48938 : List PrefixCut := [⟨28,108759481,108759540⟩,
⟨64,250057646,250057788⟩]
theorem checked48938 : checkPrefixCuts (2^48) 6418333697 10 Manual.Count131072.C048938.packed 64 cuts48938 = true := by
 decide +kernel
def pointBounds48938 : List (Nat × Nat × Nat) := [(6418391040,111389646029199,111390032998962)]
theorem point_links_checked48938 : (cuts48938.take 1).map (fun c => (6418333697-1+2*2^10*c.k,111389537269718+c.lower,111389924239422+c.upper)) = pointBounds48938 := by
 decide +kernel
def cuts48939 : List PrefixCut := [⟨62,243430744,243430888⟩,
⟨64,251017321,251017469⟩]
theorem checked48939 : checkPrefixCuts (2^48) 6418464769 10 Manual.Count131072.C048939.packed 64 cuts48939 = true := by
 decide +kernel
def pointBounds48939 : List (Nat × Nat × Nat) := [(6418591744,111390030758108,111390417728098)]
theorem point_links_checked48939 : (cuts48939.take 1).map (fun c => (6418464769-1+2*2^10*c.k,111389787327364+c.lower,111390174297210+c.upper)) = pointBounds48939 := by
 decide +kernel
def cuts48940 : List PrefixCut := [⟨64,252283911,252284061⟩]
theorem checked48940 : checkPrefixCuts (2^48) 6418595841 10 Manual.Count131072.C048940.packed 64 cuts48940 = true := by
 decide +kernel
def cuts48941 : List PrefixCut := [⟨32,125767294,125767366⟩,
⟨64,252015658,252015805⟩]
theorem checked48941 : checkPrefixCuts (2^48) 6418726913 10 Manual.Count131072.C048941.packed 64 cuts48941 = true := by
 decide +kernel
def pointBounds48941 : List (Nat × Nat × Nat) := [(6418792448,111390416395890,111390803366106)]
theorem point_links_checked48941 : (cuts48941.take 1).map (fun c => (6418726913-1+2*2^10*c.k,111390290628596+c.lower,111390677598740+c.upper)) = pointBounds48941 := by
 decide +kernel
def cuts48942 : List PrefixCut := [⟨64,253019096,253019241⟩]
theorem checked48942 : checkPrefixCuts (2^48) 6418857985 10 Manual.Count131072.C048942.packed 64 cuts48942 = true := by
 decide +kernel
def cuts48943 : List PrefixCut := [⟨2,8682366,8682371⟩,
⟨64,253320887,253321031⟩]
theorem checked48943 : checkPrefixCuts (2^48) 6418989057 10 Manual.Count131072.C048943.packed 64 cuts48943 = true := by
 decide +kernel
def pointBounds48943 : List (Nat × Nat × Nat) := [(6418993152,111390804345716,111391191316157)]
theorem point_links_checked48943 : (cuts48943.take 1).map (fun c => (6418989057-1+2*2^10*c.k,111390795663350+c.lower,111391182633786+c.upper)) = pointBounds48943 := by
 decide +kernel
def cuts48944 : List PrefixCut := [⟨36,144483114,144483194⟩,
⟨64,255508156,255508299⟩]
theorem checked48944 : checkPrefixCuts (2^48) 6419120129 10 Manual.Count131072.C048944.packed 64 cuts48944 = true := by
 decide +kernel
def pointBounds48944 : List (Nat × Nat × Nat) := [(6419193856,111391193467351,111391580438011)]
theorem point_links_checked48944 : (cuts48944.take 1).map (fun c => (6419120129-1+2*2^10*c.k,111391048984237+c.lower,111391435954817+c.upper)) = pointBounds48944 := by
 decide +kernel
def cuts48945 : List PrefixCut := [⟨64,257344535,257344681⟩]
theorem checked48945 : checkPrefixCuts (2^48) 6419251201 10 Manual.Count131072.C048945.packed 64 cuts48945 = true := by
 decide +kernel
def cuts48946 : List PrefixCut := [⟨6,23458477,23458489⟩,
⟨64,251989939,251990082⟩]
theorem checked48946 : checkPrefixCuts (2^48) 6419382273 10 Manual.Count131072.C048946.packed 64 cuts48946 = true := by
 decide +kernel
def pointBounds48946 : List (Nat × Nat × Nat) := [(6419394560,111391585295405,111391972266286)]
theorem point_links_checked48946 : (cuts48946.take 1).map (fun c => (6419382273-1+2*2^10*c.k,111391561836928+c.lower,111391948807797+c.upper)) = pointBounds48946 := by
 decide +kernel
def cuts48947 : List PrefixCut := [⟨40,156488113,156488200⟩,
⟨64,251765556,251765697⟩]
theorem checked48947 : checkPrefixCuts (2^48) 6419513345 10 Manual.Count131072.C048947.packed 64 cuts48947 = true := by
 decide +kernel
def pointBounds48947 : List (Nat × Nat × Nat) := [(6419595264,111391970314980,111392357286079)]
theorem point_links_checked48947 : (cuts48947.take 1).map (fun c => (6419513345-1+2*2^10*c.k,111391813826867+c.lower,111392200797879+c.upper)) = pointBounds48947 := by
 decide +kernel
def cuts48948 : List PrefixCut := [⟨64,256188810,256188959⟩]
theorem checked48948 : checkPrefixCuts (2^48) 6419644417 10 Manual.Count131072.C048948.packed 64 cuts48948 = true := by
 decide +kernel
def cuts48949 : List PrefixCut := [⟨10,40775763,40775784⟩,
⟨64,256928942,256929088⟩]
theorem checked48949 : checkPrefixCuts (2^48) 6419775489 10 Manual.Count131072.C048949.packed 64 cuts48949 = true := by
 decide +kernel
def pointBounds48949 : List (Nat × Nat × Nat) := [(6419795968,111392362556996,111392749528319)]
theorem point_links_checked48949 : (cuts48949.take 1).map (fun c => (6419775489-1+2*2^10*c.k,111392321781233+c.lower,111392708752535+c.upper)) = pointBounds48949 := by
 decide +kernel
def cuts48950 : List PrefixCut := [⟨44,176734235,176734333⟩,
⟨64,257537483,257537628⟩]
theorem checked48950 : checkPrefixCuts (2^48) 6419906561 10 Manual.Count131072.C048950.packed 64 cuts48950 = true := by
 decide +kernel
def pointBounds48950 : List (Nat × Nat × Nat) := [(6419996672,111392755444410,111393142415956)]
theorem point_links_checked48950 : (cuts48950.take 1).map (fun c => (6419906561-1+2*2^10*c.k,111392578710175+c.lower,111392965681623+c.upper)) = pointBounds48950 := by
 decide +kernel
def cuts48951 : List PrefixCut := [⟨64,258540605,258540750⟩]
theorem checked48951 : checkPrefixCuts (2^48) 6420037633 10 Manual.Count131072.C048951.packed 64 cuts48951 = true := by
 decide +kernel
def cuts48952 : List PrefixCut := [⟨14,55591901,55591932⟩,
⟨64,255203357,255203504⟩]
theorem checked48952 : checkPrefixCuts (2^48) 6420168705 10 Manual.Count131072.C048952.packed 64 cuts48952 = true := by
 decide +kernel
def pointBounds48952 : List (Nat × Nat × Nat) := [(6420197376,111393150380164,111393537351933)]
theorem point_links_checked48952 : (cuts48952.take 1).map (fun c => (6420168705-1+2*2^10*c.k,111393094788263+c.lower,111393481760001+c.upper)) = pointBounds48952 := by
 decide +kernel
def cuts48953 : List PrefixCut := [⟨48,189612599,189612704⟩,
⟨64,252655396,252655538⟩]
theorem checked48953 : checkPrefixCuts (2^48) 6420299777 10 Manual.Count131072.C048953.packed 64 cuts48953 = true := by
 decide +kernel
def pointBounds48953 : List (Nat × Nat × Nat) := [(6420398080,111393539604219,111393926576209)]
theorem point_links_checked48953 : (cuts48953.take 1).map (fun c => (6420299777-1+2*2^10*c.k,111393349991620+c.lower,111393736963505+c.upper)) = pointBounds48953 := by
 decide +kernel
def cuts48954 : List PrefixCut := [⟨64,255192954,255193100⟩]
theorem checked48954 : checkPrefixCuts (2^48) 6420430849 10 Manual.Count131072.C048954.packed 64 cuts48954 = true := by
 decide +kernel
def cuts48955 : List PrefixCut := [⟨18,71063798,71063837⟩,
⟨64,250759984,250760126⟩]
theorem checked48955 : checkPrefixCuts (2^48) 6420561921 10 Manual.Count131072.C048955.packed 64 cuts48955 = true := by
 decide +kernel
def pointBounds48955 : List (Nat × Nat × Nat) := [(6420598784,111393928903768,111394315875980)]
theorem point_links_checked48955 : (cuts48955.take 1).map (fun c => (6420561921-1+2*2^10*c.k,111393857839970+c.lower,111394244812143+c.upper)) = pointBounds48955 := by
 decide +kernel
def cuts48956 : List PrefixCut := [⟨52,208889713,208889830⟩,
⟨64,255620911,255621057⟩]
theorem checked48956 : checkPrefixCuts (2^48) 6420692993 10 Manual.Count131072.C048956.packed 64 cuts48956 = true := by
 decide +kernel
def pointBounds48956 : List (Nat × Nat × Nat) := [(6420799488,111394317489667,111394704462099)]
theorem point_links_checked48956 : (cuts48956.take 1).map (fun c => (6420692993-1+2*2^10*c.k,111394108599954+c.lower,111394495572269+c.upper)) = pointBounds48956 := by
 decide +kernel
def cuts48957 : List PrefixCut := [⟨64,253511470,253511609⟩]
theorem checked48957 : checkPrefixCuts (2^48) 6420824065 10 Manual.Count131072.C048957.packed 64 cuts48957 = true := by
 decide +kernel
def cuts48958 : List PrefixCut := [⟨22,87629693,87629743⟩,
⟨64,257232409,257232554⟩]
theorem checked48958 : checkPrefixCuts (2^48) 6420955137 10 Manual.Count131072.C048958.packed 64 cuts48958 = true := by
 decide +kernel
def pointBounds48958 : List (Nat × Nat × Nat) := [(6421000192,111394705362028,111395092334678)]
theorem point_links_checked48958 : (cuts48958.take 1).map (fun c => (6420955137-1+2*2^10*c.k,111394617732335+c.lower,111395004704935+c.upper)) = pointBounds48958 := by
 decide +kernel
def cuts48959 : List PrefixCut := [⟨56,219616522,219616648⟩,
⟨64,250476493,250476638⟩]
theorem checked48959 : checkPrefixCuts (2^48) 6421086209 10 Manual.Count131072.C048959.packed 64 cuts48959 = true := by
 decide +kernel
def pointBounds48959 : List (Nat × Nat × Nat) := [(6421200896,111395094581266,111395481554137)]
theorem point_links_checked48959 : (cuts48959.take 1).map (fun c => (6421086209-1+2*2^10*c.k,111394874964744+c.lower,111395261937489+c.upper)) = pointBounds48959 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000279
