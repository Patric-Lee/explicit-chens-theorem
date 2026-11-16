import PlattAssemblyKernel
import PlattCertificates.Count131072.C058032
import PlattCertificates.Count131072.C058033
import PlattCertificates.Count131072.C058034
import PlattCertificates.Count131072.C058035
import PlattCertificates.Count131072.C058036
import PlattCertificates.Count131072.C058037
import PlattCertificates.Count131072.C058038
import PlattCertificates.Count131072.C058039
import PlattCertificates.Count131072.C058040
import PlattCertificates.Count131072.C058041
import PlattCertificates.Count131072.C058042
import PlattCertificates.Count131072.C058043
import PlattCertificates.Count131072.C058044
import PlattCertificates.Count131072.C058045
import PlattCertificates.Count131072.C058046
import PlattCertificates.Count131072.C058047
import PlattCertificates.Count131072.C058048
import PlattCertificates.Count131072.C058049
import PlattCertificates.Count131072.C058050
import PlattCertificates.Count131072.C058051
import PlattCertificates.Count131072.C058052
import PlattCertificates.Count131072.C058053
import PlattCertificates.Count131072.C058054
import PlattCertificates.Count131072.C058055
import PlattCertificates.Count131072.C058056
import PlattCertificates.Count131072.C058057
import PlattCertificates.Count131072.C058058
import PlattCertificates.Count131072.C058059
import PlattCertificates.Count131072.C058060
import PlattCertificates.Count131072.C058061
import PlattCertificates.Count131072.C058062
import PlattCertificates.Count131072.C058063
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000251
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts58032 : List PrefixCut := [⟨64,212334993,212335118⟩]
theorem checked58032 : checkPrefixCuts (2^48) 7610302465 10 Manual.Count131072.C058032.packed 64 cuts58032 = true := by
 decide +kernel
def cuts58033 : List PrefixCut := [⟨18,59287449,59287482⟩,
⟨64,214809321,214809440⟩]
theorem checked58033 : checkPrefixCuts (2^48) 7610433537 10 Manual.Count131072.C058033.packed 64 cuts58033 = true := by
 decide +kernel
def pointBounds58033 : List (Nat × Nat × Nat) := [(7610470400,113504997283544,113505385455843)]
theorem point_links_checked58033 : (cuts58033.take 1).map (fun c => (7610433537-1+2*2^10*c.k,113504937996095+c.lower,113505326168361+c.upper)) = pointBounds58033 := by
 decide +kernel
def cuts58034 : List PrefixCut := [⟨64,212253707,212253830⟩]
theorem checked58034 : checkPrefixCuts (2^48) 7610564609 10 Manual.Count131072.C058034.packed 64 cuts58034 = true := by
 decide +kernel
def cuts58035 : List PrefixCut := [⟨7,22967118,22967131⟩,
⟨64,210400861,210400978⟩]
theorem checked58035 : checkPrefixCuts (2^48) 7610695681 10 Manual.Count131072.C058035.packed 64 cuts58035 = true := by
 decide +kernel
def pointBounds58035 : List (Nat × Nat × Nat) := [(7610710016,113505388026241,113505776198762)]
theorem point_links_checked58035 : (cuts58035.take 1).map (fun c => (7610695681-1+2*2^10*c.k,113505365059123+c.lower,113505753231631+c.upper)) = pointBounds58035 := by
 decide +kernel
def cuts58036 : List PrefixCut := [⟨60,200374925,200375039⟩,
⟨64,213503843,213503965⟩]
theorem checked58036 : checkPrefixCuts (2^48) 7610826753 10 Manual.Count131072.C058036.packed 64 cuts58036 = true := by
 decide +kernel
def pointBounds58036 : List (Nat × Nat × Nat) := [(7610949632,113505775834909,113506164007648)]
theorem point_links_checked58036 : (cuts58036.take 1).map (fun c => (7610826753-1+2*2^10*c.k,113505575459984+c.lower,113505963632609+c.upper)) = pointBounds58036 := by
 decide +kernel
def cuts58037 : List PrefixCut := [⟨64,210837412,210837532⟩]
theorem checked58037 : checkPrefixCuts (2^48) 7610957825 10 Manual.Count131072.C058037.packed 64 cuts58037 = true := by
 decide +kernel
def cuts58038 : List PrefixCut := [⟨49,160908548,160908641⟩,
⟨64,210389995,210390116⟩]
theorem checked58038 : checkPrefixCuts (2^48) 7611088897 10 Manual.Count131072.C058038.packed 64 cuts58038 = true := by
 decide +kernel
def pointBounds58038 : List (Nat × Nat × Nat) := [(7611189248,113506160709787,113506548882747)]
theorem point_links_checked58038 : (cuts58038.take 1).map (fun c => (7611088897-1+2*2^10*c.k,113505999801239+c.lower,113506387974106+c.upper)) = pointBounds58038 := by
 decide +kernel
def cuts58039 : List PrefixCut := [⟨64,214639200,214639322⟩]
theorem checked58039 : checkPrefixCuts (2^48) 7611219969 10 Manual.Count131072.C058039.packed 64 cuts58039 = true := by
 decide +kernel
def cuts58040 : List PrefixCut := [⟨38,125475680,125475753⟩,
⟨64,213156283,213156407⟩]
theorem checked58040 : checkPrefixCuts (2^48) 7611351041 10 Manual.Count131072.C058040.packed 64 cuts58040 = true := by
 decide +kernel
def pointBounds58040 : List (Nat × Nat × Nat) := [(7611428864,113506550306114,113506938479297)]
theorem point_links_checked58040 : (cuts58040.take 1).map (fun c => (7611351041-1+2*2^10*c.k,113506424830434+c.lower,113506813003544+c.upper)) = pointBounds58040 := by
 decide +kernel
def cuts58041 : List PrefixCut := [⟨64,213226569,213226692⟩]
theorem checked58041 : checkPrefixCuts (2^48) 7611482113 10 Manual.Count131072.C058041.packed 64 cuts58041 = true := by
 decide +kernel
def cuts58042 : List PrefixCut := [⟨27,91154539,91154591⟩,
⟨64,213148959,213149082⟩]
theorem checked58042 : checkPrefixCuts (2^48) 7611613185 10 Manual.Count131072.C058042.packed 64 cuts58042 = true := by
 decide +kernel
def pointBounds58042 : List (Nat × Nat × Nat) := [(7611668480,113506942367825,113507330541234)]
theorem point_links_checked58042 : (cuts58042.take 1).map (fun c => (7611613185-1+2*2^10*c.k,113506851213286+c.lower,113507239386643+c.upper)) = pointBounds58042 := by
 decide +kernel
def cuts58043 : List PrefixCut := [⟨64,212368731,212368855⟩]
theorem checked58043 : checkPrefixCuts (2^48) 7611744257 10 Manual.Count131072.C058043.packed 64 cuts58043 = true := by
 decide +kernel
def cuts58044 : List PrefixCut := [⟨16,52915962,52915990⟩,
⟨64,209443790,209443910⟩]
theorem checked58044 : checkPrefixCuts (2^48) 7611875329 10 Manual.Count131072.C058044.packed 64 cuts58044 = true := by
 decide +kernel
def pointBounds58044 : List (Nat × Nat × Nat) := [(7611908096,113507329646938,113507717820570)]
theorem point_links_checked58044 : (cuts58044.take 1).map (fun c => (7611875329-1+2*2^10*c.k,113507276730976+c.lower,113507664904580+c.upper)) = pointBounds58044 := by
 decide +kernel
def cuts58045 : List PrefixCut := [⟨64,215023791,215023910⟩]
theorem checked58045 : checkPrefixCuts (2^48) 7612006401 10 Manual.Count131072.C058045.packed 64 cuts58045 = true := by
 decide +kernel
def cuts58046 : List PrefixCut := [⟨5,15493401,15493410⟩,
⟨64,209177737,209177858⟩]
theorem checked58046 : checkPrefixCuts (2^48) 7612137473 10 Manual.Count131072.C058046.packed 64 cuts58046 = true := by
 decide +kernel
def pointBounds58046 : List (Nat × Nat × Nat) := [(7612147712,113507716691958,113508104865810)]
theorem point_links_checked58046 : (cuts58046.take 1).map (fun c => (7612137473-1+2*2^10*c.k,113507701198557+c.lower,113508089372400+c.upper)) = pointBounds58046 := by
 decide +kernel
def cuts58047 : List PrefixCut := [⟨58,194088032,194088144⟩,
⟨64,215423111,215423234⟩]
theorem checked58047 : checkPrefixCuts (2^48) 7612268545 10 Manual.Count131072.C058047.packed 64 cuts58047 = true := by
 decide +kernel
def pointBounds58047 : List (Nat × Nat × Nat) := [(7612387328,113508104464326,113508492638402)]
theorem point_links_checked58047 : (cuts58047.take 1).map (fun c => (7612268545-1+2*2^10*c.k,113507910376294+c.lower,113508298550258+c.upper)) = pointBounds58047 := by
 decide +kernel
def cuts58048 : List PrefixCut := [⟨64,211758840,211758963⟩]
theorem checked58048 : checkPrefixCuts (2^48) 7612399617 10 Manual.Count131072.C058048.packed 64 cuts58048 = true := by
 decide +kernel
def cuts58049 : List PrefixCut := [⟨47,159288192,159288284⟩,
⟨64,214269504,214269628⟩]
theorem checked58049 : checkPrefixCuts (2^48) 7612530689 10 Manual.Count131072.C058049.packed 64 cuts58049 = true := by
 decide +kernel
def pointBounds58049 : List (Nat × Nat × Nat) := [(7612626944,113508496846437,113508885020739)]
theorem point_links_checked58049 : (cuts58049.take 1).map (fun c => (7612530689-1+2*2^10*c.k,113508337558245+c.lower,113508725732455+c.upper)) = pointBounds58049 := by
 decide +kernel
def cuts58050 : List PrefixCut := [⟨64,213711172,213711294⟩]
theorem checked58050 : checkPrefixCuts (2^48) 7612661761 10 Manual.Count131072.C058050.packed 64 cuts58050 = true := by
 decide +kernel
def cuts58051 : List PrefixCut := [⟨36,117354692,117354761⟩,
⟨64,209566439,209566560⟩]
theorem checked58051 : checkPrefixCuts (2^48) 7612792833 10 Manual.Count131072.C058051.packed 64 cuts58051 = true := by
 decide +kernel
def pointBounds58051 : List (Nat × Nat × Nat) := [(7612866560,113508882893613,113509271068138)]
theorem point_links_checked58051 : (cuts58051.take 1).map (fun c => (7612792833-1+2*2^10*c.k,113508765538921+c.lower,113509153713377+c.upper)) = pointBounds58051 := by
 decide +kernel
def cuts58052 : List PrefixCut := [⟨64,214997874,214997997⟩]
theorem checked58052 : checkPrefixCuts (2^48) 7612923905 10 Manual.Count131072.C058052.packed 64 cuts58052 = true := by
 decide +kernel
def cuts58053 : List PrefixCut := [⟨25,81931143,81931189⟩,
⟨64,211222985,211223104⟩]
theorem checked58053 : checkPrefixCuts (2^48) 7613054977 10 Manual.Count131072.C058053.packed 64 cuts58053 = true := by
 decide +kernel
def pointBounds58053 : List (Nat × Nat × Nat) := [(7613106176,113509272034377,113509660209123)]
theorem point_links_checked58053 : (cuts58053.take 1).map (fun c => (7613054977-1+2*2^10*c.k,113509190103234+c.lower,113509578277934+c.upper)) = pointBounds58053 := by
 decide +kernel
def cuts58054 : List PrefixCut := [⟨64,214583764,214583886⟩]
theorem checked58054 : checkPrefixCuts (2^48) 7613186049 10 Manual.Count131072.C058054.packed 64 cuts58054 = true := by
 decide +kernel
def cuts58055 : List PrefixCut := [⟨14,46990547,46990571⟩,
⟨64,213397030,213397150⟩]
theorem checked58055 : checkPrefixCuts (2^48) 7613317121 10 Manual.Count131072.C058055.packed 64 cuts58055 = true := by
 decide +kernel
def pointBounds58055 : List (Nat × Nat × Nat) := [(7613345792,113509662900530,113510051075495)]
theorem point_links_checked58055 : (cuts58055.take 1).map (fun c => (7613317121-1+2*2^10*c.k,113509615909983+c.lower,113510004084924+c.upper)) = pointBounds58055 := by
 decide +kernel
def cuts58056 : List PrefixCut := [⟨64,211101168,211101292⟩]
theorem checked58056 : checkPrefixCuts (2^48) 7613448193 10 Manual.Count131072.C058056.packed 64 cuts58056 = true := by
 decide +kernel
def cuts58057 : List PrefixCut := [⟨3,9760106,9760112⟩,
⟨64,211910868,211910991⟩]
theorem checked58057 : checkPrefixCuts (2^48) 7613579265 10 Manual.Count131072.C058057.packed 64 cuts58057 = true := by
 decide +kernel
def pointBounds58057 : List (Nat × Nat × Nat) := [(7613585408,113510050168287,113510438343478)]
theorem point_links_checked58057 : (cuts58057.take 1).map (fun c => (7613579265-1+2*2^10*c.k,113510040408181+c.lower,113510428583366+c.upper)) = pointBounds58057 := by
 decide +kernel
def cuts58058 : List PrefixCut := [⟨56,187101122,187101229⟩,
⟨64,213312059,213312181⟩]
theorem checked58058 : checkPrefixCuts (2^48) 7613710337 10 Manual.Count131072.C058058.packed 64 cuts58058 = true := by
 decide +kernel
def pointBounds58058 : List (Nat × Nat × Nat) := [(7613825024,113510439420171,113510827595586)]
theorem point_links_checked58058 : (cuts58058.take 1).map (fun c => (7613710337-1+2*2^10*c.k,113510252319049+c.lower,113510640494357+c.upper)) = pointBounds58058 := by
 decide +kernel
def cuts58059 : List PrefixCut := [⟨64,211496924,211497046⟩]
theorem checked58059 : checkPrefixCuts (2^48) 7613841409 10 Manual.Count131072.C058059.packed 64 cuts58059 = true := by
 decide +kernel
def cuts58060 : List PrefixCut := [⟨45,152492916,152493000⟩,
⟨64,216853620,216853736⟩]
theorem checked58060 : checkPrefixCuts (2^48) 7613972481 10 Manual.Count131072.C058060.packed 64 cuts58060 = true := by
 decide +kernel
def pointBounds58060 : List (Nat × Nat × Nat) := [(7614064640,113510829620948,113511217796584)]
theorem point_links_checked58060 : (cuts58060.take 1).map (fun c => (7613972481-1+2*2^10*c.k,113510677128032+c.lower,113511065303584+c.upper)) = pointBounds58060 := by
 decide +kernel
def cuts58061 : List PrefixCut := [⟨64,213190128,213190252⟩]
theorem checked58061 : checkPrefixCuts (2^48) 7614103553 10 Manual.Count131072.C058061.packed 64 cuts58061 = true := by
 decide +kernel
def cuts58062 : List PrefixCut := [⟨34,113081335,113081401⟩,
⟨64,214147593,214147717⟩]
theorem checked58062 : checkPrefixCuts (2^48) 7614234625 10 Manual.Count131072.C058062.packed 64 cuts58062 = true := by
 decide +kernel
def pointBounds58062 : List (Nat × Nat × Nat) := [(7614304256,113511220253115,113511608428973)]
theorem point_links_checked58062 : (cuts58062.take 1).map (fun c => (7614234625-1+2*2^10*c.k,113511107171780+c.lower,113511495347572+c.upper)) = pointBounds58062 := by
 decide +kernel
def cuts58063 : List PrefixCut := [⟨64,212443463,212443586⟩]
theorem checked58063 : checkPrefixCuts (2^48) 7614365697 10 Manual.Count131072.C058063.packed 64 cuts58063 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000251
