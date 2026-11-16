import PlattAssemblyKernel
import PlattCertificates.Count131072.C076048
import PlattCertificates.Count131072.C076049
import PlattCertificates.Count131072.C076050
import PlattCertificates.Count131072.C076051
import PlattCertificates.Count131072.C076052
import PlattCertificates.Count131072.C076053
import PlattCertificates.Count131072.C076054
import PlattCertificates.Count131072.C076055
import PlattCertificates.Count131072.C076056
import PlattCertificates.Count131072.C076057
import PlattCertificates.Count131072.C076058
import PlattCertificates.Count131072.C076059
import PlattCertificates.Count131072.C076060
import PlattCertificates.Count131072.C076061
import PlattCertificates.Count131072.C076062
import PlattCertificates.Count131072.C076063
import PlattCertificates.Count131072.C076064
import PlattCertificates.Count131072.C076065
import PlattCertificates.Count131072.C076066
import PlattCertificates.Count131072.C076067
import PlattCertificates.Count131072.C076068
import PlattCertificates.Count131072.C076069
import PlattCertificates.Count131072.C076070
import PlattCertificates.Count131072.C076071
import PlattCertificates.Count131072.C076072
import PlattCertificates.Count131072.C076073
import PlattCertificates.Count131072.C076074
import PlattCertificates.Count131072.C076075
import PlattCertificates.Count131072.C076076
import PlattCertificates.Count131072.C076077
import PlattCertificates.Count131072.C076078
import PlattCertificates.Count131072.C076079
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000189
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts76048 : List PrefixCut := [⟨19,47788870,47788897⟩,
⟨64,161205539,161205629⟩]
theorem checked76048 : checkPrefixCuts (2^48) 9971695617 10 Manual.Count131072.C076048.packed 64 cuts76048 = true := by
 decide +kernel
def pointBounds76048 : List (Nat × Nat × Nat) := [(9971734528,116828415787523,116828805896934)]
theorem point_links_checked76048 : (cuts76048.take 1).map (fun c => (9971695617-1+2*2^10*c.k,116828367998653+c.lower,116828758108037+c.upper)) = pointBounds76048 := by
 decide +kernel
def cuts76049 : List PrefixCut := [⟨64,161429228,161429326⟩]
theorem checked76049 : checkPrefixCuts (2^48) 9971826689 10 Manual.Count131072.C076049.packed 64 cuts76049 = true := by
 decide +kernel
def cuts76050 : List PrefixCut := [⟨44,112567346,112567411⟩,
⟨64,160806146,160806236⟩]
theorem checked76050 : checkPrefixCuts (2^48) 9971957761 10 Manual.Count131072.C076050.packed 64 cuts76050 = true := by
 decide +kernel
def pointBounds76050 : List (Nat × Nat × Nat) := [(9972047872,116828803200766,116829193310403)]
theorem point_links_checked76050 : (cuts76050.take 1).map (fun c => (9971957761-1+2*2^10*c.k,116828690633420+c.lower,116829080742992+c.upper)) = pointBounds76050 := by
 decide +kernel
def cuts76051 : List PrefixCut := [⟨64,159590289,159590389⟩]
theorem checked76051 : checkPrefixCuts (2^48) 9972088833 10 Manual.Count131072.C076051.packed 64 cuts76051 = true := by
 decide +kernel
def cuts76052 : List PrefixCut := [⟨64,159447068,159447166⟩]
theorem checked76052 : checkPrefixCuts (2^48) 9972219905 10 Manual.Count131072.C076052.packed 64 cuts76052 = true := by
 decide +kernel
def cuts76053 : List PrefixCut := [⟨5,12052295,12052302⟩,
⟨64,158654659,158654761⟩]
theorem checked76053 : checkPrefixCuts (2^48) 9972350977 10 Manual.Count131072.C076053.packed 64 cuts76053 = true := by
 decide +kernel
def pointBounds76053 : List (Nat × Nat × Nat) := [(9972361216,116829182529218,116829572639085)]
theorem point_links_checked76053 : (cuts76053.take 1).map (fun c => (9972350977-1+2*2^10*c.k,116829170476923+c.lower,116829560586783+c.upper)) = pointBounds76053 := by
 decide +kernel
def cuts76054 : List PrefixCut := [⟨64,161785547,161785644⟩]
theorem checked76054 : checkPrefixCuts (2^48) 9972482049 10 Manual.Count131072.C076054.packed 64 cuts76054 = true := by
 decide +kernel
def cuts76055 : List PrefixCut := [⟨30,75896222,75896270⟩,
⟨64,161952771,161952867⟩]
theorem checked76055 : checkPrefixCuts (2^48) 9972613121 10 Manual.Count131072.C076055.packed 64 cuts76055 = true := by
 decide +kernel
def pointBounds76055 : List (Nat × Nat × Nat) := [(9972674560,116829566813351,116829956923458)]
theorem point_links_checked76055 : (cuts76055.take 1).map (fun c => (9972613121-1+2*2^10*c.k,116829490917129+c.lower,116829881027188+c.upper)) = pointBounds76055 := by
 decide +kernel
def cuts76056 : List PrefixCut := [⟨64,158112141,158112233⟩]
theorem checked76056 : checkPrefixCuts (2^48) 9972744193 10 Manual.Count131072.C076056.packed 64 cuts76056 = true := by
 decide +kernel
def cuts76057 : List PrefixCut := [⟨55,137055194,137055283⟩,
⟨64,160113958,160114062⟩]
theorem checked76057 : checkPrefixCuts (2^48) 9972875265 10 Manual.Count131072.C076057.packed 64 cuts76057 = true := by
 decide +kernel
def pointBounds76057 : List (Nat × Nat × Nat) := [(9972987904,116829948037235,116830338147571)]
theorem point_links_checked76057 : (cuts76057.take 1).map (fun c => (9972875265-1+2*2^10*c.k,116829810982041+c.lower,116830201092288+c.upper)) = pointBounds76057 := by
 decide +kernel
def cuts76058 : List PrefixCut := [⟨64,159744956,159745053⟩]
theorem checked76058 : checkPrefixCuts (2^48) 9973006337 10 Manual.Count131072.C076058.packed 64 cuts76058 = true := by
 decide +kernel
def cuts76059 : List PrefixCut := [⟨64,156497200,156497296⟩]
theorem checked76059 : checkPrefixCuts (2^48) 9973137409 10 Manual.Count131072.C076059.packed 64 cuts76059 = true := by
 decide +kernel
def cuts76060 : List PrefixCut := [⟨16,40161169,40161195⟩,
⟨64,160361653,160361747⟩]
theorem checked76060 : checkPrefixCuts (2^48) 9973268481 10 Manual.Count131072.C076060.packed 64 cuts76060 = true := by
 decide +kernel
def pointBounds76060 : List (Nat × Nat × Nat) := [(9973301248,116830327499324,116830717609894)]
theorem point_links_checked76060 : (cuts76060.take 1).map (fun c => (9973268481-1+2*2^10*c.k,116830287338155+c.lower,116830677448699+c.upper)) = pointBounds76060 := by
 decide +kernel
def cuts76061 : List PrefixCut := [⟨64,161657770,161657868⟩]
theorem checked76061 : checkPrefixCuts (2^48) 9973399553 10 Manual.Count131072.C076061.packed 64 cuts76061 = true := by
 decide +kernel
def cuts76062 : List PrefixCut := [⟨41,103208118,103208178⟩,
⟨64,159990555,159990651⟩]
theorem checked76062 : checkPrefixCuts (2^48) 9973530625 10 Manual.Count131072.C076062.packed 64 cuts76062 = true := by
 decide +kernel
def pointBounds76062 : List (Nat × Nat × Nat) := [(9973614592,116830712565696,116831102676492)]
theorem point_links_checked76062 : (cuts76062.take 1).map (fun c => (9973530625-1+2*2^10*c.k,116830609357578+c.lower,116830999468314+c.upper)) = pointBounds76062 := by
 decide +kernel
def cuts76063 : List PrefixCut := [⟨64,159678004,159678101⟩]
theorem checked76063 : checkPrefixCuts (2^48) 9973661697 10 Manual.Count131072.C076063.packed 64 cuts76063 = true := by
 decide +kernel
def cuts76064 : List PrefixCut := [⟨64,159647695,159647791⟩]
theorem checked76064 : checkPrefixCuts (2^48) 9973792769 10 Manual.Count131072.C076064.packed 64 cuts76064 = true := by
 decide +kernel
def cuts76065 : List PrefixCut := [⟨2,4600034,4600038⟩,
⟨64,159363378,159363480⟩]
theorem checked76065 : checkPrefixCuts (2^48) 9973923841 10 Manual.Count131072.C076065.packed 64 cuts76065 = true := by
 decide +kernel
def pointBounds76065 : List (Nat × Nat × Nat) := [(9973927936,116831093273866,116831483384895)]
theorem point_links_checked76065 : (cuts76065.take 1).map (fun c => (9973923841-1+2*2^10*c.k,116831088673832+c.lower,116831478784857+c.upper)) = pointBounds76065 := by
 decide +kernel
def cuts76066 : List PrefixCut := [⟨64,160151467,160151564⟩]
theorem checked76066 : checkPrefixCuts (2^48) 9974054913 10 Manual.Count131072.C076066.packed 64 cuts76066 = true := by
 decide +kernel
def cuts76067 : List PrefixCut := [⟨27,68236586,68236627⟩,
⟨64,160431564,160431662⟩]
theorem checked76067 : checkPrefixCuts (2^48) 9974185985 10 Manual.Count131072.C076067.packed 64 cuts76067 = true := by
 decide +kernel
def pointBounds76067 : List (Nat × Nat × Nat) := [(9974241280,116831476425263,116831866536528)]
theorem point_links_checked76067 : (cuts76067.take 1).map (fun c => (9974185985-1+2*2^10*c.k,116831408188677+c.lower,116831798299901+c.upper)) = pointBounds76067 := by
 decide +kernel
def cuts76068 : List PrefixCut := [⟨64,162320172,162320273⟩]
theorem checked76068 : checkPrefixCuts (2^48) 9974317057 10 Manual.Count131072.C076068.packed 64 cuts76068 = true := by
 decide +kernel
def cuts76069 : List PrefixCut := [⟨52,131728373,131728456⟩,
⟨64,163249287,163249385⟩]
theorem checked76069 : checkPrefixCuts (2^48) 9974448129 10 Manual.Count131072.C076069.packed 64 cuts76069 = true := by
 decide +kernel
def pointBounds76069 : List (Nat × Nat × Nat) := [(9974554624,116831862668786,116832252780292)]
theorem point_links_checked76069 : (cuts76069.take 1).map (fun c => (9974448129-1+2*2^10*c.k,116831730940413+c.lower,116832121051836+c.upper)) = pointBounds76069 := by
 decide +kernel
def cuts76070 : List PrefixCut := [⟨64,158591007,158591099⟩]
theorem checked76070 : checkPrefixCuts (2^48) 9974579201 10 Manual.Count131072.C076070.packed 64 cuts76070 = true := by
 decide +kernel
def cuts76071 : List PrefixCut := [⟨64,158024538,158024639⟩]
theorem checked76071 : checkPrefixCuts (2^48) 9974710273 10 Manual.Count131072.C076071.packed 64 cuts76071 = true := by
 decide +kernel
def cuts76072 : List PrefixCut := [⟨13,33015579,33015600⟩,
⟨64,161070050,161070140⟩]
theorem checked76072 : checkPrefixCuts (2^48) 9974841345 10 Manual.Count131072.C076072.packed 64 cuts76072 = true := by
 decide +kernel
def pointBounds76072 : List (Nat × Nat × Nat) := [(9974867968,116832243820824,116832633932559)]
theorem point_links_checked76072 : (cuts76072.take 1).map (fun c => (9974841345-1+2*2^10*c.k,116832210805245+c.lower,116832600916959+c.upper)) = pointBounds76072 := by
 decide +kernel
def cuts76073 : List PrefixCut := [⟨64,162281293,162281395⟩]
theorem checked76073 : checkPrefixCuts (2^48) 9974972417 10 Manual.Count131072.C076073.packed 64 cuts76073 = true := by
 decide +kernel
def cuts76074 : List PrefixCut := [⟨38,95827078,95827132⟩,
⟨64,160981159,160981254⟩]
theorem checked76074 : checkPrefixCuts (2^48) 9975103489 10 Manual.Count131072.C076074.packed 64 cuts76074 = true := by
 decide +kernel
def pointBounds76074 : List (Nat × Nat × Nat) := [(9975181312,116832629983666,116833020095626)]
theorem point_links_checked76074 : (cuts76074.take 1).map (fun c => (9975103489-1+2*2^10*c.k,116832534156588+c.lower,116832924268494+c.upper)) = pointBounds76074 := by
 decide +kernel
def cuts76075 : List PrefixCut := [⟨64,160245400,160245493⟩]
theorem checked76075 : checkPrefixCuts (2^48) 9975234561 10 Manual.Count131072.C076075.packed 64 cuts76075 = true := by
 decide +kernel
def cuts76076 : List PrefixCut := [⟨63,154882121,154882216⟩,
⟨64,157562701,157562798⟩]
theorem checked76076 : checkPrefixCuts (2^48) 9975365633 10 Manual.Count131072.C076076.packed 64 cuts76076 = true := by
 decide +kernel
def pointBounds76076 : List (Nat × Nat × Nat) := [(9975494656,116833010265268,116833400377457)]
theorem point_links_checked76076 : (cuts76076.take 1).map (fun c => (9975365633-1+2*2^10*c.k,116832855383147+c.lower,116833245495241+c.upper)) = pointBounds76076 := by
 decide +kernel
def cuts76077 : List PrefixCut := [⟨64,160015451,160015549⟩]
theorem checked76077 : checkPrefixCuts (2^48) 9975496705 10 Manual.Count131072.C076077.packed 64 cuts76077 = true := by
 decide +kernel
def cuts76078 : List PrefixCut := [⟨64,159646549,159646646⟩]
theorem checked76078 : checkPrefixCuts (2^48) 9975627777 10 Manual.Count131072.C076078.packed 64 cuts76078 = true := by
 decide +kernel
def cuts76079 : List PrefixCut := [⟨24,60635791,60635831⟩,
⟨64,161506678,161506776⟩]
theorem checked76079 : checkPrefixCuts (2^48) 9975758849 10 Manual.Count131072.C076079.packed 64 cuts76079 = true := by
 decide +kernel
def pointBounds76079 : List (Nat × Nat × Nat) := [(9975808000,116833393243639,116833783356065)]
theorem point_links_checked76079 : (cuts76079.take 1).map (fun c => (9975758849-1+2*2^10*c.k,116833332607848+c.lower,116833722720234+c.upper)) = pointBounds76079 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000189
