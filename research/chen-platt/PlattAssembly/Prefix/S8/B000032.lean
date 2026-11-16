import PlattAssemblyKernel
import PlattCertificates.Count131072.C071024
import PlattCertificates.Count131072.C071025
import PlattCertificates.Count131072.C071026
import PlattCertificates.Count131072.C071027
import PlattCertificates.Count131072.C071028
import PlattCertificates.Count131072.C071029
import PlattCertificates.Count131072.C071030
import PlattCertificates.Count131072.C071031
import PlattCertificates.Count131072.C071032
import PlattCertificates.Count131072.C071033
import PlattCertificates.Count131072.C071034
import PlattCertificates.Count131072.C071035
import PlattCertificates.Count131072.C071036
import PlattCertificates.Count131072.C071037
import PlattCertificates.Count131072.C071038
import PlattCertificates.Count131072.C071039
import PlattCertificates.Count131072.C071040
import PlattCertificates.Count131072.C071041
import PlattCertificates.Count131072.C071042
import PlattCertificates.Count131072.C071043
import PlattCertificates.Count131072.C071044
import PlattCertificates.Count131072.C071045
import PlattCertificates.Count131072.C071046
import PlattCertificates.Count131072.C071047
import PlattCertificates.Count131072.C071048
import PlattCertificates.Count131072.C071049
import PlattCertificates.Count131072.C071050
import PlattCertificates.Count131072.C071051
import PlattCertificates.Count131072.C071052
import PlattCertificates.Count131072.C071053
import PlattCertificates.Count131072.C071054
import PlattCertificates.Count131072.C071055
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000032
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71024 : List PrefixCut := [⟨64,174175377,174175483⟩]
theorem checked71024 : checkPrefixCuts (2^48) 9313189889 10 Manual.Count131072.C071024.packed 64 cuts71024 = true := by
 decide +kernel
def cuts71025 : List PrefixCut := [⟨64,173205802,173205905⟩]
theorem checked71025 : checkPrefixCuts (2^48) 9313320961 10 Manual.Count131072.C071025.packed 64 cuts71025 = true := by
 decide +kernel
def cuts71026 : List PrefixCut := [⟨5,13600073,13600083⟩,
⟨64,173082481,173082590⟩]
theorem checked71026 : checkPrefixCuts (2^48) 9313452033 10 Manual.Count131072.C071026.packed 64 cuts71026 = true := by
 decide +kernel
def pointBounds71026 : List (Nat × Nat × Nat) := [(9313462272,115992185803829,115992575414211)]
theorem point_links_checked71026 : (cuts71026.take 1).map (fun c => (9313452033-1+2*2^10*c.k,115992172203756+c.lower,115992561814128+c.upper)) = pointBounds71026 := by
 decide +kernel
def cuts71027 : List PrefixCut := [⟨64,171417842,171417945⟩]
theorem checked71027 : checkPrefixCuts (2^48) 9313583105 10 Manual.Count131072.C071027.packed 64 cuts71027 = true := by
 decide +kernel
def cuts71028 : List PrefixCut := [⟨20,56091077,56091108⟩,
⟨64,173379839,173379944⟩]
theorem checked71028 : checkPrefixCuts (2^48) 9313714177 10 Manual.Count131072.C071028.packed 64 cuts71028 = true := by
 decide +kernel
def pointBounds71028 : List (Nat × Nat × Nat) := [(9313755136,115992572795156,115992962405771)]
theorem point_links_checked71028 : (cuts71028.take 1).map (fun c => (9313714177-1+2*2^10*c.k,115992516704079+c.lower,115992906314663+c.upper)) = pointBounds71028 := by
 decide +kernel
def cuts71029 : List PrefixCut := [⟨64,173196062,173196161⟩]
theorem checked71029 : checkPrefixCuts (2^48) 9313845249 10 Manual.Count131072.C071029.packed 64 cuts71029 = true := by
 decide +kernel
def cuts71030 : List PrefixCut := [⟨35,92354108,92354161⟩,
⟨64,170503990,170504089⟩]
theorem checked71030 : checkPrefixCuts (2^48) 9313976321 10 Manual.Count131072.C071030.packed 64 cuts71030 = true := by
 decide +kernel
def pointBounds71030 : List (Nat × Nat × Nat) := [(9314048000,115992955634088,115993345244929)]
theorem point_links_checked71030 : (cuts71030.take 1).map (fun c => (9313976321-1+2*2^10*c.k,115992863279980+c.lower,115993252890768+c.upper)) = pointBounds71030 := by
 decide +kernel
def cuts71031 : List PrefixCut := [⟨64,170652701,170652798⟩]
theorem checked71031 : checkPrefixCuts (2^48) 9314107393 10 Manual.Count131072.C071031.packed 64 cuts71031 = true := by
 decide +kernel
def cuts71032 : List PrefixCut := [⟨50,135353966,135354047⟩,
⟨64,173521157,173521263⟩]
theorem checked71032 : checkPrefixCuts (2^48) 9314238465 10 Manual.Count131072.C071032.packed 64 cuts71032 = true := by
 decide +kernel
def pointBounds71032 : List (Nat × Nat × Nat) := [(9314340864,115993339790637,115993729401702)]
theorem point_links_checked71032 : (cuts71032.take 1).map (fun c => (9314238465-1+2*2^10*c.k,115993204436671+c.lower,115993594047655+c.upper)) = pointBounds71032 := by
 decide +kernel
def cuts71033 : List PrefixCut := [⟨64,174334629,174334734⟩]
theorem checked71033 : checkPrefixCuts (2^48) 9314369537 10 Manual.Count131072.C071033.packed 64 cuts71033 = true := by
 decide +kernel
def cuts71034 : List PrefixCut := [⟨64,173848688,173848790⟩]
theorem checked71034 : checkPrefixCuts (2^48) 9314500609 10 Manual.Count131072.C071034.packed 64 cuts71034 = true := by
 decide +kernel
def cuts71035 : List PrefixCut := [⟨1,2961420,2961422⟩,
⟨64,172637516,172637618⟩]
theorem checked71035 : checkPrefixCuts (2^48) 9314631681 10 Manual.Count131072.C071035.packed 64 cuts71035 = true := by
 decide +kernel
def pointBounds71035 : List (Nat × Nat × Nat) := [(9314633728,115993729102565,115994118713864)]
theorem point_links_checked71035 : (cuts71035.take 1).map (fun c => (9314631681-1+2*2^10*c.k,115993726141145+c.lower,115994115752442+c.upper)) = pointBounds71035 := by
 decide +kernel
def cuts71036 : List PrefixCut := [⟨64,172060924,172061024⟩]
theorem checked71036 : checkPrefixCuts (2^48) 9314762753 10 Manual.Count131072.C071036.packed 64 cuts71036 = true := by
 decide +kernel
def cuts71037 : List PrefixCut := [⟨16,42848656,42848681⟩,
⟨64,172088721,172088826⟩]
theorem checked71037 : checkPrefixCuts (2^48) 9314893825 10 Manual.Count131072.C071037.packed 64 cuts71037 = true := by
 decide +kernel
def pointBounds71037 : List (Nat × Nat × Nat) := [(9314926592,115994113688241,115994503299765)]
theorem point_links_checked71037 : (cuts71037.take 1).map (fun c => (9314893825-1+2*2^10*c.k,115994070839585+c.lower,115994460451084+c.upper)) = pointBounds71037 := by
 decide +kernel
def cuts71038 : List PrefixCut := [⟨64,175651912,175652018⟩]
theorem checked71038 : checkPrefixCuts (2^48) 9315024897 10 Manual.Count131072.C071038.packed 64 cuts71038 = true := by
 decide +kernel
def cuts71039 : List PrefixCut := [⟨31,82975258,82975307⟩,
⟨64,170452195,170452294⟩]
theorem checked71039 : checkPrefixCuts (2^48) 9315155969 10 Manual.Count131072.C071039.packed 64 cuts71039 = true := by
 decide +kernel
def pointBounds71039 : List (Nat × Nat × Nat) := [(9315219456,115994501555476,115994891167235)]
theorem point_links_checked71039 : (cuts71039.take 1).map (fun c => (9315155969-1+2*2^10*c.k,115994418580218+c.lower,115994808191928+c.upper)) = pointBounds71039 := by
 decide +kernel
def cuts71040 : List PrefixCut := [⟨64,172987942,172988044⟩]
theorem checked71040 : checkPrefixCuts (2^48) 9315287041 10 Manual.Count131072.C071040.packed 64 cuts71040 = true := by
 decide +kernel
def cuts71041 : List PrefixCut := [⟨46,125093706,125093782⟩,
⟨64,174315014,174315119⟩]
theorem checked71041 : checkPrefixCuts (2^48) 9315418113 10 Manual.Count131072.C071041.packed 64 cuts71041 = true := by
 decide +kernel
def pointBounds71041 : List (Nat × Nat × Nat) := [(9315512320,115994887114061,115995276726048)]
theorem point_links_checked71041 : (cuts71041.take 1).map (fun c => (9315418113-1+2*2^10*c.k,115994762020355+c.lower,115995151632266+c.upper)) = pointBounds71041 := by
 decide +kernel
def cuts71042 : List PrefixCut := [⟨64,174282344,174282445⟩]
theorem checked71042 : checkPrefixCuts (2^48) 9315549185 10 Manual.Count131072.C071042.packed 64 cuts71042 = true := by
 decide +kernel
def cuts71043 : List PrefixCut := [⟨61,166242769,166242860⟩,
⟨64,174642472,174642568⟩]
theorem checked71043 : checkPrefixCuts (2^48) 9315680257 10 Manual.Count131072.C071043.packed 64 cuts71043 = true := by
 decide +kernel
def pointBounds71043 : List (Nat × Nat × Nat) := [(9315805184,115995276860482,115995666472690)]
theorem point_links_checked71043 : (cuts71043.take 1).map (fun c => (9315680257-1+2*2^10*c.k,115995110617713+c.lower,115995500229830+c.upper)) = pointBounds71043 := by
 decide +kernel
def cuts71044 : List PrefixCut := [⟨64,173038630,173038739⟩]
theorem checked71044 : checkPrefixCuts (2^48) 9315811329 10 Manual.Count131072.C071044.packed 64 cuts71044 = true := by
 decide +kernel
def cuts71045 : List PrefixCut := [⟨64,172492345,172492445⟩]
theorem checked71045 : checkPrefixCuts (2^48) 9315942401 10 Manual.Count131072.C071045.packed 64 cuts71045 = true := by
 decide +kernel
def cuts71046 : List PrefixCut := [⟨12,31936047,31936065⟩,
⟨64,173003559,173003659⟩]
theorem checked71046 : checkPrefixCuts (2^48) 9316073473 10 Manual.Count131072.C071046.packed 64 cuts71046 = true := by
 decide +kernel
def pointBounds71046 : List (Nat × Nat × Nat) := [(9316098048,115995662727207,115996052339647)]
theorem point_links_checked71046 : (cuts71046.take 1).map (fun c => (9316073473-1+2*2^10*c.k,115995630791160+c.lower,115996020403582+c.upper)) = pointBounds71046 := by
 decide +kernel
def cuts71047 : List PrefixCut := [⟨64,172759420,172759520⟩]
theorem checked71047 : checkPrefixCuts (2^48) 9316204545 10 Manual.Count131072.C071047.packed 64 cuts71047 = true := by
 decide +kernel
def cuts71048 : List PrefixCut := [⟨27,70426407,70426446⟩,
⟨64,168738679,168738777⟩]
theorem checked71048 : checkPrefixCuts (2^48) 9316335617 10 Manual.Count131072.C071048.packed 64 cuts71048 = true := by
 decide +kernel
def pointBounds71048 : List (Nat × Nat × Nat) := [(9316390912,115996046980546,115996436593207)]
theorem point_links_checked71048 : (cuts71048.take 1).map (fun c => (9316335617-1+2*2^10*c.k,115995976554139+c.lower,115996366166761+c.upper)) = pointBounds71048 := by
 decide +kernel
def cuts71049 : List PrefixCut := [⟨64,175503893,175504003⟩]
theorem checked71049 : checkPrefixCuts (2^48) 9316466689 10 Manual.Count131072.C071049.packed 64 cuts71049 = true := by
 decide +kernel
def cuts71050 : List PrefixCut := [⟨42,113023307,113023377⟩,
⟨64,173235515,173235622⟩]
theorem checked71050 : checkPrefixCuts (2^48) 9316597761 10 Manual.Count131072.C071050.packed 64 cuts71050 = true := by
 decide +kernel
def pointBounds71050 : List (Nat × Nat × Nat) := [(9316683776,115996433820018,115996823432918)]
theorem point_links_checked71050 : (cuts71050.take 1).map (fun c => (9316597761-1+2*2^10*c.k,115996320796711+c.lower,115996710409541+c.upper)) = pointBounds71050 := by
 decide +kernel
def cuts71051 : List PrefixCut := [⟨64,171299547,171299645⟩]
theorem checked71051 : checkPrefixCuts (2^48) 9316728833 10 Manual.Count131072.C071051.packed 64 cuts71051 = true := by
 decide +kernel
def cuts71052 : List PrefixCut := [⟨57,152868453,152868545⟩,
⟨64,172324303,172324406⟩]
theorem checked71052 : checkPrefixCuts (2^48) 9316859905 10 Manual.Count131072.C071052.packed 64 cuts71052 = true := by
 decide +kernel
def pointBounds71052 : List (Nat × Nat × Nat) := [(9316976640,115996818200226,115997207813353)]
theorem point_links_checked71052 : (cuts71052.take 1).map (fun c => (9316859905-1+2*2^10*c.k,115996665331773+c.lower,115997054944808+c.upper)) = pointBounds71052 := by
 decide +kernel
def cuts71053 : List PrefixCut := [⟨64,173077154,173077260⟩]
theorem checked71053 : checkPrefixCuts (2^48) 9316990977 10 Manual.Count131072.C071053.packed 64 cuts71053 = true := by
 decide +kernel
def cuts71054 : List PrefixCut := [⟨64,172349669,172349776⟩]
theorem checked71054 : checkPrefixCuts (2^48) 9317122049 10 Manual.Count131072.C071054.packed 64 cuts71054 = true := by
 decide +kernel
def cuts71055 : List PrefixCut := [⟨8,22566904,22566918⟩,
⟨64,173555654,173555756⟩]
theorem checked71055 : checkPrefixCuts (2^48) 9317253121 10 Manual.Count131072.C071055.packed 64 cuts71055 = true := by
 decide +kernel
def pointBounds71055 : List (Nat × Nat × Nat) := [(9317269504,115997205649803,115997595263168)]
theorem point_links_checked71055 : (cuts71055.take 1).map (fun c => (9317253121-1+2*2^10*c.k,115997183082899+c.lower,115997572696250+c.upper)) = pointBounds71055 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000032
