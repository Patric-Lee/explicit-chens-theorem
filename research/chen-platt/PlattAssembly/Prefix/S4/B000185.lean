import PlattAssemblyKernel
import PlattCertificates.Count131072.C035920
import PlattCertificates.Count131072.C035921
import PlattCertificates.Count131072.C035922
import PlattCertificates.Count131072.C035923
import PlattCertificates.Count131072.C035924
import PlattCertificates.Count131072.C035925
import PlattCertificates.Count131072.C035926
import PlattCertificates.Count131072.C035927
import PlattCertificates.Count131072.C035928
import PlattCertificates.Count131072.C035929
import PlattCertificates.Count131072.C035930
import PlattCertificates.Count131072.C035931
import PlattCertificates.Count131072.C035932
import PlattCertificates.Count131072.C035933
import PlattCertificates.Count131072.C035934
import PlattCertificates.Count131072.C035935
import PlattCertificates.Count131072.C035936
import PlattCertificates.Count131072.C035937
import PlattCertificates.Count131072.C035938
import PlattCertificates.Count131072.C035939
import PlattCertificates.Count131072.C035940
import PlattCertificates.Count131072.C035941
import PlattCertificates.Count131072.C035942
import PlattCertificates.Count131072.C035943
import PlattCertificates.Count131072.C035944
import PlattCertificates.Count131072.C035945
import PlattCertificates.Count131072.C035946
import PlattCertificates.Count131072.C035947
import PlattCertificates.Count131072.C035948
import PlattCertificates.Count131072.C035949
import PlattCertificates.Count131072.C035950
import PlattCertificates.Count131072.C035951
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000185
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts35920 : List PrefixCut := [⟨64,350939867,350940082⟩]
theorem checked35920 : checkPrefixCuts (2^48) 4712038401 10 Manual.Count131072.C035920.packed 64 cuts35920 = true := by
 decide +kernel
def cuts35921 : List PrefixCut := [⟨8,45457196,45457224⟩,
⟨64,355410053,355410269⟩]
theorem checked35921 : checkPrefixCuts (2^48) 4712169473 10 Manual.Count131072.C035921.packed 64 cuts35921 = true := by
 decide +kernel
def pointBounds35921 : List (Nat × Nat × Nat) := [(4712185856,107511404768587,107511789454610)]
theorem point_links_checked35921 : (cuts35921.take 1).map (fun c => (4712169473-1+2*2^10*c.k,107511359311391+c.lower,107511743997386+c.upper)) = pointBounds35921 := by
 decide +kernel
def cuts35922 : List PrefixCut := [⟨16,86670756,86670810⟩,
⟨64,348769976,348770190⟩]
theorem checked35922 : checkPrefixCuts (2^48) 4712300545 10 Manual.Count131072.C035922.packed 64 cuts35922 = true := by
 decide +kernel
def pointBounds35922 : List (Nat × Nat × Nat) := [(4712333312,107511801392200,107512186078465)]
theorem point_links_checked35922 : (cuts35922.take 1).map (fun c => (4712300545-1+2*2^10*c.k,107511714721444+c.lower,107512099407655+c.upper)) = pointBounds35922 := by
 decide +kernel
def cuts35923 : List PrefixCut := [⟨24,133078377,133078461⟩,
⟨64,358257259,358257477⟩]
theorem checked35923 : checkPrefixCuts (2^48) 4712431617 10 Manual.Count131072.C035923.packed 64 cuts35923 = true := by
 decide +kernel
def pointBounds35923 : List (Nat × Nat × Nat) := [(4712480768,107512196569797,107512581256306)]
theorem point_links_checked35923 : (cuts35923.take 1).map (fun c => (4712431617-1+2*2^10*c.k,107512063491420+c.lower,107512448177845+c.upper)) = pointBounds35923 := by
 decide +kernel
def cuts35924 : List PrefixCut := [⟨32,172733990,172734097⟩,
⟨64,348750575,348750792⟩]
theorem checked35924 : checkPrefixCuts (2^48) 4712562689 10 Manual.Count131072.C035924.packed 64 cuts35924 = true := by
 decide +kernel
def pointBounds35924 : List (Nat × Nat × Nat) := [(4712628224,107512594482669,107512979169419)]
theorem point_links_checked35924 : (cuts35924.take 1).map (fun c => (4712562689-1+2*2^10*c.k,107512421748679+c.lower,107512806435322+c.upper)) = pointBounds35924 := by
 decide +kernel
def cuts35925 : List PrefixCut := [⟨40,218479323,218479458⟩,
⟨64,346471313,346471531⟩]
theorem checked35925 : checkPrefixCuts (2^48) 4712693761 10 Manual.Count131072.C035925.packed 64 cuts35925 = true := by
 decide +kernel
def pointBounds35925 : List (Nat × Nat × Nat) := [(4712775680,107512988978577,107513373665572)]
theorem point_links_checked35925 : (cuts35925.take 1).map (fun c => (4712693761-1+2*2^10*c.k,107512770499254+c.lower,107513155186114+c.upper)) = pointBounds35925 := by
 decide +kernel
def cuts35926 : List PrefixCut := [⟨48,263565038,263565201⟩,
⟨64,353270258,353270478⟩]
theorem checked35926 : checkPrefixCuts (2^48) 4712824833 10 Manual.Count131072.C035926.packed 64 cuts35926 = true := by
 decide +kernel
def pointBounds35926 : List (Nat × Nat × Nat) := [(4712923136,107513380535605,107513765222846)]
theorem point_links_checked35926 : (cuts35926.take 1).map (fun c => (4712824833-1+2*2^10*c.k,107513116970567+c.lower,107513501657645+c.upper)) = pointBounds35926 := by
 decide +kernel
def cuts35927 : List PrefixCut := [⟨56,311335567,311335760⟩,
⟨64,355828519,355828739⟩]
theorem checked35927 : checkPrefixCuts (2^48) 4712955905 10 Manual.Count131072.C035927.packed 64 cuts35927 = true := by
 decide +kernel
def pointBounds35927 : List (Nat × Nat × Nat) := [(4713070592,107513781576392,107514166263883)]
theorem point_links_checked35927 : (cuts35927.take 1).map (fun c => (4712955905-1+2*2^10*c.k,107513470240825+c.lower,107513854928123+c.upper)) = pointBounds35927 := by
 decide +kernel
def cuts35928 : List PrefixCut := [⟨64,356296432,356296655⟩]
theorem checked35928 : checkPrefixCuts (2^48) 4713086977 10 Manual.Count131072.C035928.packed 64 cuts35928 = true := by
 decide +kernel
def pointBounds35928 : List (Nat × Nat × Nat) := [(4713218048,107514182365776,107514567053517)]
theorem point_links_checked35928 : (cuts35928.take 1).map (fun c => (4713086977-1+2*2^10*c.k,107513826069344+c.lower,107514210756862+c.upper)) = pointBounds35928 := by
 decide +kernel
def cuts35929 : List PrefixCut := [⟨64,351807505,351807719⟩]
theorem checked35929 : checkPrefixCuts (2^48) 4713218049 10 Manual.Count131072.C035929.packed 64 cuts35929 = true := by
 decide +kernel
def cuts35930 : List PrefixCut := [⟨8,46520755,46520783⟩,
⟨64,348513286,348513500⟩]
theorem checked35930 : checkPrefixCuts (2^48) 4713349121 10 Manual.Count131072.C035930.packed 64 cuts35930 = true := by
 decide +kernel
def pointBounds35930 : List (Nat × Nat × Nat) := [(4713365504,107514580694036,107514965382019)]
theorem point_links_checked35930 : (cuts35930.take 1).map (fun c => (4713349121-1+2*2^10*c.k,107514534173281+c.lower,107514918861236+c.upper)) = pointBounds35930 := by
 decide +kernel
def cuts35931 : List PrefixCut := [⟨16,86947648,86947699⟩,
⟨64,354714000,354714220⟩]
theorem checked35931 : checkPrefixCuts (2^48) 4713480193 10 Manual.Count131072.C035931.packed 64 cuts35931 = true := by
 decide +kernel
def pointBounds35931 : List (Nat × Nat × Nat) := [(4713512960,107514969634215,107515354322435)]
theorem point_links_checked35931 : (cuts35931.take 1).map (fun c => (4713480193-1+2*2^10*c.k,107514882686567+c.lower,107515267374736+c.upper)) = pointBounds35931 := by
 decide +kernel
def cuts35932 : List PrefixCut := [⟨24,131134196,131134274⟩,
⟨64,347837032,347837245⟩]
theorem checked35932 : checkPrefixCuts (2^48) 4713611265 10 Manual.Count131072.C035932.packed 64 cuts35932 = true := by
 decide +kernel
def pointBounds35932 : List (Nat × Nat × Nat) := [(4713660416,107515368534763,107515753223230)]
theorem point_links_checked35932 : (cuts35932.take 1).map (fun c => (4713611265-1+2*2^10*c.k,107515237400567+c.lower,107515622088956+c.upper)) = pointBounds35932 := by
 decide +kernel
def cuts35933 : List PrefixCut := [⟨32,174303012,174303126⟩,
⟨64,353022328,353022551⟩]
theorem checked35933 : checkPrefixCuts (2^48) 4713742337 10 Manual.Count131072.C035933.packed 64 cuts35933 = true := by
 decide +kernel
def pointBounds35933 : List (Nat × Nat × Nat) := [(4713807872,107515759540611,107516144229327)]
theorem point_links_checked35933 : (cuts35933.take 1).map (fun c => (4713742337-1+2*2^10*c.k,107515585237599+c.lower,107515969926201+c.upper)) = pointBounds35933 := by
 decide +kernel
def cuts35934 : List PrefixCut := [⟨40,220633987,220634125⟩,
⟨64,355580098,355580321⟩]
theorem checked35934 : checkPrefixCuts (2^48) 4713873409 10 Manual.Count131072.C035934.packed 64 cuts35934 = true := by
 decide +kernel
def pointBounds35934 : List (Nat × Nat × Nat) := [(4713955328,107516158893914,107516543582877)]
theorem point_links_checked35934 : (cuts35934.take 1).map (fun c => (4713873409-1+2*2^10*c.k,107515938259927+c.lower,107516322948752+c.upper)) = pointBounds35934 := by
 decide +kernel
def cuts35935 : List PrefixCut := [⟨48,262722827,262722992⟩,
⟨64,351808513,351808732⟩]
theorem checked35935 : checkPrefixCuts (2^48) 4714004481 10 Manual.Count131072.C035935.packed 64 cuts35935 = true := by
 decide +kernel
def pointBounds35935 : List (Nat × Nat × Nat) := [(4714102784,107516556562852,107516941252065)]
theorem point_links_checked35935 : (cuts35935.take 1).map (fun c => (4714004481-1+2*2^10*c.k,107516293840025+c.lower,107516678529073+c.upper)) = pointBounds35935 := by
 decide +kernel
def cuts35936 : List PrefixCut := [⟨56,304152391,304152575⟩,
⟨64,348753625,348753837⟩]
theorem checked35936 : checkPrefixCuts (2^48) 4714135553 10 Manual.Count131072.C035936.packed 64 cuts35936 = true := by
 decide +kernel
def pointBounds35936 : List (Nat × Nat × Nat) := [(4714250240,107516949800929,107517334490380)]
theorem point_links_checked35936 : (cuts35936.take 1).map (fun c => (4714135553-1+2*2^10*c.k,107516645648538+c.lower,107517030337805+c.upper)) = pointBounds35936 := by
 decide +kernel
def cuts35937 : List PrefixCut := [⟨64,353281609,353281820⟩]
theorem checked35937 : checkPrefixCuts (2^48) 4714266625 10 Manual.Count131072.C035937.packed 64 cuts35937 = true := by
 decide +kernel
def pointBounds35937 : List (Nat × Nat × Nat) := [(4714397696,107517347683772,107517732373462)]
theorem point_links_checked35937 : (cuts35937.take 1).map (fun c => (4714266625-1+2*2^10*c.k,107516994402163+c.lower,107517379091642+c.upper)) = pointBounds35937 := by
 decide +kernel
def cuts35938 : List PrefixCut := [⟨64,350346276,350346499⟩]
theorem checked35938 : checkPrefixCuts (2^48) 4714397697 10 Manual.Count131072.C035938.packed 64 cuts35938 = true := by
 decide +kernel
def cuts35939 : List PrefixCut := [⟨8,43941860,43941888⟩,
⟨64,352844033,352844247⟩]
theorem checked35939 : checkPrefixCuts (2^48) 4714528769 10 Manual.Count131072.C035939.packed 64 cuts35939 = true := by
 decide +kernel
def pointBounds35939 : List (Nat × Nat × Nat) := [(4714545152,107517741971908,107518126661849)]
theorem point_links_checked35939 : (cuts35939.take 1).map (fun c => (4714528769-1+2*2^10*c.k,107517698030048+c.lower,107518082719961+c.upper)) = pointBounds35939 := by
 decide +kernel
def cuts35940 : List PrefixCut := [⟨16,89373665,89373721⟩,
⟨64,354147666,354147894⟩]
theorem checked35940 : checkPrefixCuts (2^48) 4714659841 10 Manual.Count131072.C035940.packed 64 cuts35940 = true := by
 decide +kernel
def pointBounds35940 : List (Nat × Nat × Nat) := [(4714692608,107518140247746,107518524937929)]
theorem point_links_checked35940 : (cuts35940.take 1).map (fun c => (4714659841-1+2*2^10*c.k,107518050874081+c.lower,107518435564208+c.upper)) = pointBounds35940 := by
 decide +kernel
def cuts35941 : List PrefixCut := [⟨24,133847602,133847684⟩,
⟨64,353302069,353302285⟩]
theorem checked35941 : checkPrefixCuts (2^48) 4714790913 10 Manual.Count131072.C035941.packed 64 cuts35941 = true := by
 decide +kernel
def pointBounds35941 : List (Nat × Nat × Nat) := [(4714840064,107518538869349,107518923559786)]
theorem point_links_checked35941 : (cuts35941.take 1).map (fun c => (4714790913-1+2*2^10*c.k,107518405021747+c.lower,107518789712102+c.upper)) = pointBounds35941 := by
 decide +kernel
def cuts35942 : List PrefixCut := [⟨32,177005518,177005625⟩,
⟨64,350964021,350964237⟩]
theorem checked35942 : checkPrefixCuts (2^48) 4714921985 10 Manual.Count131072.C035942.packed 64 cuts35942 = true := by
 decide +kernel
def pointBounds35942 : List (Nat × Nat × Nat) := [(4714987520,107518935329334,107519320020012)]
theorem point_links_checked35942 : (cuts35942.take 1).map (fun c => (4714921985-1+2*2^10*c.k,107518758323816+c.lower,107519143014387+c.upper)) = pointBounds35942 := by
 decide +kernel
def cuts35943 : List PrefixCut := [⟨40,218250592,218250726⟩,
⟨64,349879686,349879900⟩]
theorem checked35943 : checkPrefixCuts (2^48) 4715053057 10 Manual.Count131072.C035943.packed 64 cuts35943 = true := by
 decide +kernel
def pointBounds35943 : List (Nat × Nat × Nat) := [(4715134976,107519327538429,107519712229350)]
theorem point_links_checked35943 : (cuts35943.take 1).map (fun c => (4715053057-1+2*2^10*c.k,107519109287837+c.lower,107519493978624+c.upper)) = pointBounds35943 := by
 decide +kernel
def cuts35944 : List PrefixCut := [⟨48,261045324,261045489⟩,
⟨64,350049028,350049246⟩]
theorem checked35944 : checkPrefixCuts (2^48) 4715184129 10 Manual.Count131072.C035944.packed 64 cuts35944 = true := by
 decide +kernel
def pointBounds35944 : List (Nat × Nat × Nat) := [(4715282432,107519720212847,107520104904013)]
theorem point_links_checked35944 : (cuts35944.take 1).map (fun c => (4715184129-1+2*2^10*c.k,107519459167523+c.lower,107519843858524+c.upper)) = pointBounds35944 := by
 decide +kernel
def cuts35945 : List PrefixCut := [⟨56,306165554,306165747⟩,
⟨64,350158709,350158929⟩]
theorem checked35945 : checkPrefixCuts (2^48) 4715315201 10 Manual.Count131072.C035945.packed 64 cuts35945 = true := by
 decide +kernel
def pointBounds35945 : List (Nat × Nat × Nat) := [(4715429888,107520115382105,107520500073517)]
theorem point_links_checked35945 : (cuts35945.take 1).map (fun c => (4715315201-1+2*2^10*c.k,107519809216551+c.lower,107520193907770+c.upper)) = pointBounds35945 := by
 decide +kernel
def cuts35946 : List PrefixCut := [⟨64,349253598,349253813⟩]
theorem checked35946 : checkPrefixCuts (2^48) 4715446273 10 Manual.Count131072.C035946.packed 64 cuts35946 = true := by
 decide +kernel
def pointBounds35946 : List (Nat × Nat × Nat) := [(4715577344,107520508628858,107520893320512)]
theorem point_links_checked35946 : (cuts35946.take 1).map (fun c => (4715446273-1+2*2^10*c.k,107520159375260+c.lower,107520544066699+c.upper)) = pointBounds35946 := by
 decide +kernel
def cuts35947 : List PrefixCut := [⟨64,349602026,349602246⟩]
theorem checked35947 : checkPrefixCuts (2^48) 4715577345 10 Manual.Count131072.C035947.packed 64 cuts35947 = true := by
 decide +kernel
def cuts35948 : List PrefixCut := [⟨8,42975845,42975873⟩,
⟨64,352039518,352039734⟩]
theorem checked35948 : checkPrefixCuts (2^48) 4715708417 10 Manual.Count131072.C035948.packed 64 cuts35948 = true := by
 decide +kernel
def pointBounds35948 : List (Nat × Nat × Nat) := [(4715724800,107520901206729,107521285898631)]
theorem point_links_checked35948 : (cuts35948.take 1).map (fun c => (4715708417-1+2*2^10*c.k,107520858230884+c.lower,107521242922758+c.upper)) = pointBounds35948 := by
 decide +kernel
def cuts35949 : List PrefixCut := [⟨16,88873821,88873878⟩,
⟨64,350597315,350597534⟩]
theorem checked35949 : checkPrefixCuts (2^48) 4715839489 10 Manual.Count131072.C035949.packed 64 cuts35949 = true := by
 decide +kernel
def pointBounds35949 : List (Nat × Nat × Nat) := [(4715872256,107521299144223,107521683836370)]
theorem point_links_checked35949 : (cuts35949.take 1).map (fun c => (4715839489-1+2*2^10*c.k,107521210270402+c.lower,107521594962492+c.upper)) = pointBounds35949 := by
 decide +kernel
def cuts35950 : List PrefixCut := [⟨24,133515690,133515769⟩,
⟨64,351124729,351124941⟩]
theorem checked35950 : checkPrefixCuts (2^48) 4715970561 10 Manual.Count131072.C035950.packed 64 cuts35950 = true := by
 decide +kernel
def pointBounds35950 : List (Nat × Nat × Nat) := [(4716019712,107521694383407,107522079075795)]
theorem point_links_checked35950 : (cuts35950.take 1).map (fun c => (4715970561-1+2*2^10*c.k,107521560867717+c.lower,107521945560026+c.upper)) = pointBounds35950 := by
 decide +kernel
def cuts35951 : List PrefixCut := [⟨32,176722498,176722610⟩,
⟨64,352069859,352070083⟩]
theorem checked35951 : checkPrefixCuts (2^48) 4716101633 10 Manual.Count131072.C035951.packed 64 cuts35951 = true := by
 decide +kernel
def pointBounds35951 : List (Nat × Nat × Nat) := [(4716167168,107522088714944,107522473407577)]
theorem point_links_checked35951 : (cuts35951.take 1).map (fun c => (4716101633-1+2*2^10*c.k,107521911992446+c.lower,107522296684967+c.upper)) = pointBounds35951 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000185
