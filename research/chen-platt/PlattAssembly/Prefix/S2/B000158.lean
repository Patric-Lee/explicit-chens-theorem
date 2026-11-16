import PlattAssemblyKernel
import PlattCertificates.Count131072.C015056
import PlattCertificates.Count131072.C015057
import PlattCertificates.Count131072.C015058
import PlattCertificates.Count131072.C015059
import PlattCertificates.Count131072.C015060
import PlattCertificates.Count131072.C015061
import PlattCertificates.Count131072.C015062
import PlattCertificates.Count131072.C015063
import PlattCertificates.Count131072.C015064
import PlattCertificates.Count131072.C015065
import PlattCertificates.Count131072.C015066
import PlattCertificates.Count131072.C015067
import PlattCertificates.Count131072.C015068
import PlattCertificates.Count131072.C015069
import PlattCertificates.Count131072.C015070
import PlattCertificates.Count131072.C015071
import PlattCertificates.Count131072.C015072
import PlattCertificates.Count131072.C015073
import PlattCertificates.Count131072.C015074
import PlattCertificates.Count131072.C015075
import PlattCertificates.Count131072.C015076
import PlattCertificates.Count131072.C015077
import PlattCertificates.Count131072.C015078
import PlattCertificates.Count131072.C015079
import PlattCertificates.Count131072.C015080
import PlattCertificates.Count131072.C015081
import PlattCertificates.Count131072.C015082
import PlattCertificates.Count131072.C015083
import PlattCertificates.Count131072.C015084
import PlattCertificates.Count131072.C015085
import PlattCertificates.Count131072.C015086
import PlattCertificates.Count131072.C015087
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000158
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15056 : List PrefixCut := [⟨50,343769334,343769559⟩,
⟨111,759697008,759697505⟩,
⟨128,871292031,871292600⟩]
theorem checked15056 : checkPrefixCuts (2^48) 1977352193 9 Manual.Count131072.C015056.packed 128 cuts15056 = true := by
 decide +kernel
def pointBounds15056 : List (Nat × Nat × Nat) := [(1977403392,96318041914357,96318419981065),(1977465856,96318457842031,96318835909011)]
theorem point_links_checked15056 : (cuts15056.take 2).map (fun c => (1977352193-1+2*2^9*c.k,96317698145023+c.lower,96318076211506+c.upper)) = pointBounds15056 := by
 decide +kernel
def cuts15057 : List PrefixCut := [⟨44,304319375,304319578⟩,
⟨105,718370308,718370787⟩,
⟨128,875646457,875647041⟩]
theorem checked15057 : checkPrefixCuts (2^48) 1977483265 9 Manual.Count131072.C015057.packed 128 cuts15057 = true := by
 decide +kernel
def pointBounds15057 : List (Nat × Nat × Nat) := [(1977528320,96318873756429,96319251823684),(1977590784,96319287807362,96319665874893)]
theorem point_links_checked15057 : (cuts15057.take 2).map (fun c => (1977483265-1+2*2^9*c.k,96318569437054+c.lower,96318947504106+c.upper)) = pointBounds15057 := by
 decide +kernel
def cuts15058 : List PrefixCut := [⟨38,260462316,260462480⟩,
⟨99,674771799,674772240⟩,
⟨128,865910442,865911009⟩]
theorem checked15058 : checkPrefixCuts (2^48) 1977614337 9 Manual.Count131072.C015058.packed 128 cuts15058 = true := by
 decide +kernel
def pointBounds15058 : List (Nat × Nat × Nat) := [(1977653248,96319705545827,96320083613627),(1977715712,96320119855310,96320497923387)]
theorem point_links_checked15058 : (cuts15058.take 2).map (fun c => (1977614337-1+2*2^9*c.k,96319445083511+c.lower,96319823151147+c.upper)) = pointBounds15058 := by
 decide +kernel
def cuts15059 : List PrefixCut := [⟨32,221876729,221876878⟩,
⟨93,633740577,633740999⟩,
⟨128,867845355,867845933⟩]
theorem checked15059 : checkPrefixCuts (2^48) 1977745409 9 Manual.Count131072.C015059.packed 128 cuts15059 = true := by
 decide +kernel
def pointBounds15059 : List (Nat × Nat × Nat) := [(1977778176,96320532870682,96320910939034),(1977840640,96320944734530,96321322803155)]
theorem point_links_checked15059 : (cuts15059.take 2).map (fun c => (1977745409-1+2*2^9*c.k,96320310993953+c.lower,96320689062156+c.upper)) = pointBounds15059 := by
 decide +kernel
def cuts15060 : List PrefixCut := [⟨26,181730780,181730895⟩,
⟨87,592572595,592572983⟩,
⟨128,869211058,869211631⟩]
theorem checked15060 : checkPrefixCuts (2^48) 1977876481 9 Manual.Count131072.C015060.packed 128 cuts15060 = true := by
 decide +kernel
def pointBounds15060 : List (Nat × Nat × Nat) := [(1977903104,96321360570088,96321738638984),(1977965568,96321771411903,96322149481072)]
theorem point_links_checked15060 : (cuts15060.take 2).map (fun c => (1977876481-1+2*2^9*c.k,96321178839308+c.lower,96321556908089+c.upper)) = pointBounds15060 := by
 decide +kernel
def cuts15061 : List PrefixCut := [⟨20,135328716,135328808⟩,
⟨81,554682363,554682733⟩,
⟨128,874418180,874418762⟩]
theorem checked15061 : checkPrefixCuts (2^48) 1978007553 9 Manual.Count131072.C015061.packed 128 cuts15061 = true := by
 decide +kernel
def pointBounds15061 : List (Nat × Nat × Nat) := [(1978028032,96322183379082,96322561448528),(1978090496,96322602732729,96322980802453)]
theorem point_links_checked15061 : (cuts15061.take 2).map (fun c => (1978007553-1+2*2^9*c.k,96322048050366+c.lower,96322426119720+c.upper)) = pointBounds15061 := by
 decide +kernel
def cuts15062 : List PrefixCut := [⟨14,95193527,95193590⟩,
⟨75,509825185,509825526⟩,
⟨128,874787109,874787690⟩]
theorem checked15062 : checkPrefixCuts (2^48) 1978138625 9 Manual.Count131072.C015062.packed 128 cuts15062 = true := by
 decide +kernel
def pointBounds15062 : List (Nat × Nat × Nat) := [(1978152960,96323017662073,96323395732072),(1978215424,96323432293731,96323810364008)]
theorem point_links_checked15062 : (cuts15062.take 2).map (fun c => (1978138625-1+2*2^9*c.k,96322922468546+c.lower,96323300538482+c.upper)) = pointBounds15062 := by
 decide +kernel
def cuts15063 : List PrefixCut := [⟨8,50652775,50652809⟩,
⟨69,475075550,475075868⟩,
⟨128,872595027,872595613⟩]
theorem checked15063 : checkPrefixCuts (2^48) 1978269697 9 Manual.Count131072.C015063.packed 128 cuts15063 = true := by
 decide +kernel
def pointBounds15063 : List (Nat × Nat × Nat) := [(1978277888,96323847908430,96324225978981),(1978340352,96324272331205,96324650402040)]
theorem point_links_checked15063 : (cuts15063.take 2).map (fun c => (1978269697-1+2*2^9*c.k,96323797255655+c.lower,96324175326172+c.upper)) = pointBounds15063 := by
 decide +kernel
def cuts15064 : List PrefixCut := [⟨2,14511936,14511945⟩,
⟨63,424823050,424823331⟩,
⟨124,846929377,846929942⟩,
⟨128,874386458,874387041⟩]
theorem checked15064 : checkPrefixCuts (2^48) 1978400769 9 Manual.Count131072.C015064.packed 128 cuts15064 = true := by
 decide +kernel
def pointBounds15064 : List (Nat × Nat × Nat) := [(1978402816,96324684362618,96325062433730),(1978465280,96325094673732,96325472745116),(1978527744,96325516780059,96325894851727)]
theorem point_links_checked15064 : (cuts15064.take 3).map (fun c => (1978400769-1+2*2^9*c.k,96324669850682+c.lower,96325047921785+c.upper)) = pointBounds15064 := by
 decide +kernel
def cuts15065 : List PrefixCut := [⟨57,391363923,391364183⟩,
⟨118,805477199,805477735⟩,
⟨128,877316209,877316791⟩]
theorem checked15065 : checkPrefixCuts (2^48) 1978531841 9 Manual.Count131072.C015065.packed 128 cuts15065 = true := by
 decide +kernel
def pointBounds15065 : List (Nat × Nat × Nat) := [(1978590208,96325935601063,96326313673009),(1978652672,96326349714339,96326727786561)]
theorem point_links_checked15065 : (cuts15065.take 2).map (fun c => (1978531841-1+2*2^9*c.k,96325544237140+c.lower,96325922308826+c.upper)) = pointBounds15065 := by
 decide +kernel
def cuts15066 : List PrefixCut := [⟨51,352076747,352076979⟩,
⟨112,773276262,773276770⟩,
⟨128,877685020,877685595⟩]
theorem checked15066 : checkPrefixCuts (2^48) 1978662913 9 Manual.Count131072.C015066.packed 128 cuts15066 = true := by
 decide +kernel
def pointBounds15066 : List (Nat × Nat × Nat) := [(1978715136,96326773630096,96327151702596),(1978777600,96327194829611,96327572902387)]
theorem point_links_checked15066 : (cuts15066.take 2).map (fun c => (1978662913-1+2*2^9*c.k,96326421553349+c.lower,96326799625617+c.upper)) = pointBounds15066 := by
 decide +kernel
def cuts15067 : List PrefixCut := [⟨45,306678096,306678299⟩,
⟨106,722588248,722588725⟩,
⟨128,868807948,868808524⟩]
theorem checked15067 : checkPrefixCuts (2^48) 1978793985 9 Manual.Count131072.C015067.packed 128 cuts15067 = true := by
 decide +kernel
def pointBounds15067 : List (Nat × Nat × Nat) := [(1978840064,96327605916465,96327983989511),(1978902528,96328021826617,96328399899937)]
theorem point_links_checked15067 : (cuts15067.take 2).map (fun c => (1978793985-1+2*2^9*c.k,96327299238369+c.lower,96327677311212+c.upper)) = pointBounds15067 := by
 decide +kernel
def cuts15068 : List PrefixCut := [⟨39,264272277,264272447⟩,
⟨100,675462457,675462899⟩,
⟨128,864341056,864341620⟩]
theorem checked15068 : checkPrefixCuts (2^48) 1978925057 9 Manual.Count131072.C015068.packed 128 cuts15068 = true := by
 decide +kernel
def pointBounds15068 : List (Nat × Nat × Nat) := [(1978964992,96328432318594,96328810392183),(1979027456,96328843508774,96329221582635)]
theorem point_links_checked15068 : (cuts15068.take 2).map (fun c => (1978925057-1+2*2^9*c.k,96328168046317+c.lower,96328546119736+c.upper)) = pointBounds15068 := by
 decide +kernel
def cuts15069 : List PrefixCut := [⟨33,219454147,219454290⟩,
⟨94,633178370,633178787⟩,
⟨128,866132520,866133092⟩]
theorem checked15069 : checkPrefixCuts (2^48) 1979056129 9 Manual.Count131072.C015069.packed 128 cuts15069 = true := by
 decide +kernel
def pointBounds15069 : List (Nat × Nat × Nat) := [(1979089920,96329251841520,96329629915646),(1979152384,96329665565743,96330043640143)]
theorem point_links_checked15069 : (cuts15069.take 2).map (fun c => (1979056129-1+2*2^9*c.k,96329032387373+c.lower,96329410461356+c.upper)) = pointBounds15069 := by
 decide +kernel
def cuts15070 : List PrefixCut := [⟨27,183316977,183317100⟩,
⟨88,598437273,598437669⟩,
⟨128,869630742,869631319⟩]
theorem checked15070 : checkPrefixCuts (2^48) 1979187201 9 Manual.Count131072.C015070.packed 128 cuts15070 = true := by
 decide +kernel
def pointBounds15070 : List (Nat × Nat × Nat) := [(1979214848,96330081836870,96330459911548),(1979277312,96330496957166,96330875032117)]
theorem point_links_checked15070 : (cuts15070.take 2).map (fun c => (1979187201-1+2*2^9*c.k,96329898519893+c.lower,96330276594448+c.upper)) = pointBounds15070 := by
 decide +kernel
def cuts15071 : List PrefixCut := [⟨21,149033183,149033281⟩,
⟨82,561852045,561852415⟩,
⟨128,876825653,876826234⟩]
theorem checked15071 : checkPrefixCuts (2^48) 1979318273 9 Manual.Count131072.C015071.packed 128 cuts15071 = true := by
 decide +kernel
def pointBounds15071 : List (Nat × Nat × Nat) := [(1979339776,96330917183818,96331295259048),(1979402240,96331330002680,96331708078182)]
theorem point_links_checked15071 : (cuts15071.take 2).map (fun c => (1979318273-1+2*2^9*c.k,96330768150635+c.lower,96331146225767+c.upper)) = pointBounds15071 := by
 decide +kernel
def cuts15072 : List PrefixCut := [⟨15,102098183,102098252⟩,
⟨76,512615919,512616262⟩,
⟨128,871932775,871933355⟩]
theorem checked15072 : checkPrefixCuts (2^48) 1979449345 9 Manual.Count131072.C015072.packed 128 cuts15072 = true := by
 decide +kernel
def pointBounds15072 : List (Nat × Nat × Nat) := [(1979464704,96331747074471,96332125150253),(1979527168,96332157592207,96332535668263)]
theorem point_links_checked15072 : (cuts15072.take 2).map (fun c => (1979449345-1+2*2^9*c.k,96331644976288+c.lower,96332023052001+c.upper)) = pointBounds15072 := by
 decide +kernel
def cuts15073 : List PrefixCut := [⟨9,61141187,61141229⟩,
⟨70,469215731,469216041⟩,
⟨128,863628219,863628790⟩]
theorem checked15073 : checkPrefixCuts (2^48) 1979580417 9 Manual.Count131072.C015073.packed 128 cuts15073 = true := by
 decide +kernel
def pointBounds15073 : List (Nat × Nat × Nat) := [(1979589632,96332578050250,96332956126585),(1979652096,96332986124794,96333364201397)]
theorem point_links_checked15073 : (cuts15073.take 2).map (fun c => (1979580417-1+2*2^9*c.k,96332516909063+c.lower,96332894985356+c.upper)) = pointBounds15073 := by
 decide +kernel
def cuts15074 : List PrefixCut := [⟨3,23744001,23744017⟩,
⟨64,440892195,440892478⟩,
⟨125,850065550,850066106⟩,
⟨128,869969413,869969983⟩]
theorem checked15074 : checkPrefixCuts (2^48) 1979711489 9 Manual.Count131072.C015074.packed 128 cuts15074 = true := by
 decide +kernel
def pointBounds15074 : List (Nat × Nat × Nat) := [(1979714560,96333404281283,96333782358163),(1979777024,96333821429477,96334199506624),(1979839488,96334230602832,96334608680252)]
theorem point_links_checked15074 : (cuts15074.take 3).map (fun c => (1979711489-1+2*2^9*c.k,96333380537282+c.lower,96333758614146+c.upper)) = pointBounds15074 := by
 decide +kernel
def cuts15075 : List PrefixCut := [⟨58,392668526,392668790⟩,
⟨119,811056706,811057250⟩,
⟨128,869342821,869343403⟩]
theorem checked15075 : checkPrefixCuts (2^48) 1979842561 9 Manual.Count131072.C015075.packed 128 cuts15075 = true := by
 decide +kernel
def pointBounds15075 : List (Nat × Nat × Nat) := [(1979901952,96334643175221,96335021252919),(1979964416,96335061563401,96335439641379)]
theorem point_links_checked15075 : (cuts15075.take 2).map (fun c => (1979842561-1+2*2^9*c.k,96334250506695+c.lower,96334628584129+c.upper)) = pointBounds15075 := by
 decide +kernel
def cuts15076 : List PrefixCut := [⟨52,351559173,351559403⟩,
⟨113,775464969,775465479⟩,
⟨128,877530162,877530741⟩]
theorem checked15076 : checkPrefixCuts (2^48) 1979973633 9 Manual.Count131072.C015076.packed 128 cuts15076 = true := by
 decide +kernel
def pointBounds15076 : List (Nat × Nat × Nat) := [(1980026880,96335471408689,96335849486935),(1980089344,96335895314485,96336273393011)]
theorem point_links_checked15076 : (cuts15076.take 2).map (fun c => (1979973633-1+2*2^9*c.k,96335119849516+c.lower,96335497927532+c.upper)) = pointBounds15076 := by
 decide +kernel
def cuts15077 : List PrefixCut := [⟨46,305195676,305195874⟩,
⟨107,727937520,727937993⟩,
⟨128,870648968,870649538⟩]
theorem checked15077 : checkPrefixCuts (2^48) 1980104705 9 Manual.Count131072.C015077.packed 128 cuts15077 = true := by
 decide +kernel
def pointBounds15077 : List (Nat × Nat × Nat) := [(1980151808,96336302575354,96336680654147),(1980214272,96336725317198,96337103396266)]
theorem point_links_checked15077 : (cuts15077.take 2).map (fun c => (1980104705-1+2*2^9*c.k,96335997379678+c.lower,96336375458273+c.upper)) = pointBounds15077 := by
 decide +kernel
def cuts15078 : List PrefixCut := [⟨40,273620696,273620883⟩,
⟨101,683827859,683828324⟩,
⟨128,866896064,866896647⟩]
theorem checked15078 : checkPrefixCuts (2^48) 1980235777 9 Manual.Count131072.C015078.packed 128 cuts15078 = true := by
 decide +kernel
def pointBounds15078 : List (Nat × Nat × Nat) := [(1980276736,96337141649342,96337519728694),(1980339200,96337551856505,96337929936135)]
theorem point_links_checked15078 : (cuts15078.take 2).map (fun c => (1980235777-1+2*2^9*c.k,96336868028646+c.lower,96337246107811+c.upper)) = pointBounds15078 := by
 decide +kernel
def cuts15079 : List PrefixCut := [⟨34,232669183,232669338⟩,
⟨95,651378147,651378579⟩,
⟨128,873376628,873377208⟩]
theorem checked15079 : checkPrefixCuts (2^48) 1980366849 9 Manual.Count131072.C015079.packed 128 cuts15079 = true := by
 decide +kernel
def pointBounds15079 : List (Nat × Nat × Nat) := [(1980401664,96337967593893,96338345673796),(1980464128,96338386302857,96338764383037)]
theorem point_links_checked15079 : (cuts15079.take 2).map (fun c => (1980366849-1+2*2^9*c.k,96337734924710+c.lower,96338113004458+c.upper)) = pointBounds15079 := by
 decide +kernel
def cuts15080 : List PrefixCut := [⟨28,189875352,189875478⟩,
⟨89,617511406,617511815⟩,
⟨128,880282621,880283206⟩]
theorem checked15080 : checkPrefixCuts (2^48) 1980497921 9 Manual.Count131072.C015080.packed 128 cuts15080 = true := by
 decide +kernel
def pointBounds15080 : List (Nat × Nat × Nat) := [(1980526592,96338798176690,96339176257144),(1980589056,96339225812744,96339603893481)]
theorem point_links_checked15080 : (cuts15080.take 2).map (fun c => (1980497921-1+2*2^9*c.k,96338608301338+c.lower,96338986381666+c.upper)) = pointBounds15080 := by
 decide +kernel
def cuts15081 : List PrefixCut := [⟨22,148223940,148224038⟩,
⟨83,558637678,558638045⟩,
⟨128,861892127,861892697⟩]
theorem checked15081 : checkPrefixCuts (2^48) 1980628993 9 Manual.Count131072.C015081.packed 128 cuts15081 = true := by
 decide +kernel
def pointBounds15081 : List (Nat × Nat × Nat) := [(1980651520,96339636807899,96340014888910),(1980713984,96340047221637,96340425302917)]
theorem point_links_checked15081 : (cuts15081.take 2).map (fun c => (1980628993-1+2*2^9*c.k,96339488583959+c.lower,96339866664872+c.upper)) = pointBounds15081 := by
 decide +kernel
def cuts15082 : List PrefixCut := [⟨16,108709480,108709552⟩,
⟨77,526628763,526629107⟩,
⟨128,875903083,875903661⟩]
theorem checked15082 : checkPrefixCuts (2^48) 1980760065 9 Manual.Count131072.C015082.packed 128 cuts15082 = true := by
 decide +kernel
def pointBounds15082 : List (Nat × Nat × Nat) := [(1980776448,96340459185566,96340837267121),(1980838912,96340877104849,96341255186676)]
theorem point_links_checked15082 : (cuts15082.take 2).map (fun c => (1980760065-1+2*2^9*c.k,96340350476086+c.lower,96340728557569+c.upper)) = pointBounds15082 := by
 decide +kernel
def cuts15083 : List PrefixCut := [⟨10,67779178,67779222⟩,
⟨71,487661414,487661740⟩,
⟨128,870303841,870304420⟩]
theorem checked15083 : checkPrefixCuts (2^48) 1980891137 9 Manual.Count131072.C015083.packed 128 cuts15083 = true := by
 decide +kernel
def pointBounds15083 : List (Nat × Nat × Nat) := [(1980901376,96341294158347,96341672240452),(1980963840,96341714040583,96342092122970)]
theorem point_links_checked15083 : (cuts15083.take 2).map (fun c => (1980891137-1+2*2^9*c.k,96341226379169+c.lower,96341604461230+c.upper)) = pointBounds15083 := by
 decide +kernel
def cuts15084 : List PrefixCut := [⟨4,25149139,25149157⟩,
⟨65,433922357,433922644⟩,
⟨126,842540626,842541187⟩,
⟨128,856179956,856180526⟩]
theorem checked15084 : checkPrefixCuts (2^48) 1981022209 9 Manual.Count131072.C015084.packed 128 cuts15084 = true := by
 decide +kernel
def pointBounds15084 : List (Nat × Nat × Nat) := [(1981026304,96342121832149,96342499914807),(1981088768,96342530605367,96342908688294),(1981151232,96342939223636,96343317306837)]
theorem point_links_checked15084 : (cuts15084.take 3).map (fun c => (1981022209-1+2*2^9*c.k,96342096683010+c.lower,96342474765650+c.upper)) = pointBounds15084 := by
 decide +kernel
def cuts15085 : List PrefixCut := [⟨59,398091624,398091887⟩,
⟨120,820464870,820465411⟩,
⟨128,873029721,873030297⟩]
theorem checked15085 : checkPrefixCuts (2^48) 1981153281 9 Manual.Count131072.C015085.packed 128 cuts15085 = true := by
 decide +kernel
def pointBounds15085 : List (Nat × Nat × Nat) := [(1981213696,96343350954590,96343729038063),(1981276160,96343773327836,96344151411587)]
theorem point_links_checked15085 : (cuts15085.take 2).map (fun c => (1981153281-1+2*2^9*c.k,96342952862966+c.lower,96343330946176+c.upper)) = pointBounds15085 := by
 decide +kernel
def cuts15086 : List PrefixCut := [⟨53,362265664,362265907⟩,
⟨114,776230754,776231266⟩,
⟨128,871409609,871410182⟩]
theorem checked15086 : checkPrefixCuts (2^48) 1981284353 9 Manual.Count131072.C015086.packed 128 cuts15086 = true := by
 decide +kernel
def pointBounds15086 : List (Nat × Nat × Nat) := [(1981338624,96344188158351,96344566242380),(1981401088,96344602123441,96344980207739)]
theorem point_links_checked15086 : (cuts15086.take 2).map (fun c => (1981284353-1+2*2^9*c.k,96343825892687+c.lower,96344203976473+c.upper)) = pointBounds15086 := by
 decide +kernel
def cuts15087 : List PrefixCut := [⟨47,318773143,318773353⟩,
⟨108,736405485,736405972⟩,
⟨128,873198495,873199071⟩]
theorem checked15087 : checkPrefixCuts (2^48) 1981415425 9 Manual.Count131072.C015087.packed 128 cuts15087 = true := by
 decide +kernel
def pointBounds15087 : List (Nat × Nat × Nat) := [(1981463552,96345016075439,96345394160008),(1981526016,96345433707781,96345811792627)]
theorem point_links_checked15087 : (cuts15087.take 2).map (fun c => (1981415425-1+2*2^9*c.k,96344697302296+c.lower,96345075386655+c.upper)) = pointBounds15087 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000158
