import PlattAssemblyKernel
import PlattCertificates.Count131072.C038064
import PlattCertificates.Count131072.C038065
import PlattCertificates.Count131072.C038066
import PlattCertificates.Count131072.C038067
import PlattCertificates.Count131072.C038068
import PlattCertificates.Count131072.C038069
import PlattCertificates.Count131072.C038070
import PlattCertificates.Count131072.C038071
import PlattCertificates.Count131072.C038072
import PlattCertificates.Count131072.C038073
import PlattCertificates.Count131072.C038074
import PlattCertificates.Count131072.C038075
import PlattCertificates.Count131072.C038076
import PlattCertificates.Count131072.C038077
import PlattCertificates.Count131072.C038078
import PlattCertificates.Count131072.C038079
import PlattCertificates.Count131072.C038080
import PlattCertificates.Count131072.C038081
import PlattCertificates.Count131072.C038082
import PlattCertificates.Count131072.C038083
import PlattCertificates.Count131072.C038084
import PlattCertificates.Count131072.C038085
import PlattCertificates.Count131072.C038086
import PlattCertificates.Count131072.C038087
import PlattCertificates.Count131072.C038088
import PlattCertificates.Count131072.C038089
import PlattCertificates.Count131072.C038090
import PlattCertificates.Count131072.C038091
import PlattCertificates.Count131072.C038092
import PlattCertificates.Count131072.C038093
import PlattCertificates.Count131072.C038094
import PlattCertificates.Count131072.C038095
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000252
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts38064 : List PrefixCut := [⟨64,328990018,328990218⟩]
theorem checked38064 : checkPrefixCuts (2^48) 4993056769 10 Manual.Count131072.C038064.packed 64 cuts38064 = true := by
 decide +kernel
def cuts38065 : List PrefixCut := [⟨2,10541518,10541525⟩,
⟨64,328699532,328699734⟩]
theorem checked38065 : checkPrefixCuts (2^48) 4993187841 10 Manual.Count131072.C038065.packed 64 cuts38065 = true := by
 decide +kernel
def pointBounds38065 : List (Nat × Nat × Nat) := [(4993191936,108242429811952,108242814944150)]
theorem point_links_checked38065 : (cuts38065.take 1).map (fun c => (4993187841-1+2*2^10*c.k,108242419270434+c.lower,108242804402625+c.upper)) = pointBounds38065 := by
 decide +kernel
def cuts38066 : List PrefixCut := [⟨15,76494262,76494308⟩,
⟨64,329874651,329874847⟩]
theorem checked38066 : checkPrefixCuts (2^48) 4993318913 10 Manual.Count131072.C038066.packed 64 cuts38066 = true := by
 decide +kernel
def pointBounds38066 : List (Nat × Nat × Nat) := [(4993349632,108242824464228,108243209596667)]
theorem point_links_checked38066 : (cuts38066.take 1).map (fun c => (4993318913-1+2*2^10*c.k,108242747969966+c.lower,108243133102359+c.upper)) = pointBounds38066 := by
 decide +kernel
def cuts38067 : List PrefixCut := [⟨28,142048613,142048700⟩,
⟨64,325694767,325694968⟩]
theorem checked38067 : checkPrefixCuts (2^48) 4993449985 10 Manual.Count131072.C038067.packed 64 cuts38067 = true := by
 decide +kernel
def pointBounds38067 : List (Nat × Nat × Nat) := [(4993507328,108243219893230,108243605025906)]
theorem point_links_checked38067 : (cuts38067.take 1).map (fun c => (4993449985-1+2*2^10*c.k,108243077844617+c.lower,108243462977206+c.upper)) = pointBounds38067 := by
 decide +kernel
def cuts38068 : List PrefixCut := [⟨41,211432131,211432260⟩,
⟨64,329631909,329632106⟩]
theorem checked38068 : checkPrefixCuts (2^48) 4993581057 10 Manual.Count131072.C038068.packed 64 cuts38068 = true := by
 decide +kernel
def pointBounds38068 : List (Nat × Nat × Nat) := [(4993665024,108243614971515,108244000104434)]
theorem point_links_checked38068 : (cuts38068.take 1).map (fun c => (4993581057-1+2*2^10*c.k,108243403539384+c.lower,108243788672174+c.upper)) = pointBounds38068 := by
 decide +kernel
def cuts38069 : List PrefixCut := [⟨54,281262543,281262715⟩,
⟨64,333174248,333174450⟩]
theorem checked38069 : checkPrefixCuts (2^48) 4993712129 10 Manual.Count131072.C038069.packed 64 cuts38069 = true := by
 decide +kernel
def pointBounds38069 : List (Nat × Nat × Nat) := [(4993822720,108244014433836,108244399566995)]
theorem point_links_checked38069 : (cuts38069.take 1).map (fun c => (4993712129-1+2*2^10*c.k,108243733171293+c.lower,108244118304280+c.upper)) = pointBounds38069 := by
 decide +kernel
def cuts38070 : List PrefixCut := [⟨64,330572762,330572964⟩]
theorem checked38070 : checkPrefixCuts (2^48) 4993843201 10 Manual.Count131072.C038070.packed 64 cuts38070 = true := by
 decide +kernel
def cuts38071 : List PrefixCut := [⟨3,15048886,15048895⟩,
⟨64,330113170,330113370⟩]
theorem checked38071 : checkPrefixCuts (2^48) 4993974273 10 Manual.Count131072.C038071.packed 64 cuts38071 = true := by
 decide +kernel
def pointBounds38071 : List (Nat × Nat × Nat) := [(4993980416,108244411967189,108244797100589)]
theorem point_links_checked38071 : (cuts38071.take 1).map (fun c => (4993974273-1+2*2^10*c.k,108244396918303+c.lower,108244782051694+c.upper)) = pointBounds38071 := by
 decide +kernel
def cuts38072 : List PrefixCut := [⟨16,83752804,83752854⟩,
⟨64,335966027,335966229⟩]
theorem checked38072 : checkPrefixCuts (2^48) 4994105345 10 Manual.Count131072.C038072.packed 64 cuts38072 = true := by
 decide +kernel
def pointBounds38072 : List (Nat × Nat × Nat) := [(4994138112,108244810784277,108245195917918)]
theorem point_links_checked38072 : (cuts38072.take 1).map (fun c => (4994105345-1+2*2^10*c.k,108244727031473+c.lower,108245112165064+c.upper)) = pointBounds38072 := by
 decide +kernel
def cuts38073 : List PrefixCut := [⟨29,148169411,148169501⟩,
⟨64,330321285,330321487⟩]
theorem checked38073 : checkPrefixCuts (2^48) 4994236417 10 Manual.Count131072.C038073.packed 64 cuts38073 = true := by
 decide +kernel
def pointBounds38073 : List (Nat × Nat × Nat) := [(4994295808,108245211166911,108245596300794)]
theorem point_links_checked38073 : (cuts38073.take 1).map (fun c => (4994236417-1+2*2^10*c.k,108245062997500+c.lower,108245448131293+c.upper)) = pointBounds38073 := by
 decide +kernel
def cuts38074 : List PrefixCut := [⟨42,217485451,217485582⟩,
⟨64,329918152,329918350⟩]
theorem checked38074 : checkPrefixCuts (2^48) 4994367489 10 Manual.Count131072.C038074.packed 64 cuts38074 = true := by
 decide +kernel
def pointBounds38074 : List (Nat × Nat × Nat) := [(4994453504,108245610804236,108245995938362)]
theorem point_links_checked38074 : (cuts38074.take 1).map (fun c => (4994367489-1+2*2^10*c.k,108245393318785+c.lower,108245778452780+c.upper)) = pointBounds38074 := by
 decide +kernel
def cuts38075 : List PrefixCut := [⟨55,284824998,284825170⟩,
⟨64,330754820,330755022⟩]
theorem checked38075 : checkPrefixCuts (2^48) 4994498561 10 Manual.Count131072.C038075.packed 64 cuts38075 = true := by
 decide +kernel
def pointBounds38075 : List (Nat × Nat × Nat) := [(4994611200,108246008061935,108246393196300)]
theorem point_links_checked38075 : (cuts38075.take 1).map (fun c => (4994498561-1+2*2^10*c.k,108245723236937+c.lower,108246108371130+c.upper)) = pointBounds38075 := by
 decide +kernel
def cuts38076 : List PrefixCut := [⟨64,333056689,333056891⟩]
theorem checked38076 : checkPrefixCuts (2^48) 4994629633 10 Manual.Count131072.C038076.packed 64 cuts38076 = true := by
 decide +kernel
def cuts38077 : List PrefixCut := [⟨4,19780248,19780259⟩,
⟨64,330004839,330005033⟩]
theorem checked38077 : checkPrefixCuts (2^48) 4994760705 10 Manual.Count131072.C038077.packed 64 cuts38077 = true := by
 decide +kernel
def pointBounds38077 : List (Nat × Nat × Nat) := [(4994768896,108246406828694,108246791963302)]
theorem point_links_checked38077 : (cuts38077.take 1).map (fun c => (4994760705-1+2*2^10*c.k,108246387048446+c.lower,108246772183043+c.upper)) = pointBounds38077 := by
 decide +kernel
def cuts38078 : List PrefixCut := [⟨17,88022379,88022433⟩,
⟨64,326502425,326502625⟩]
theorem checked38078 : checkPrefixCuts (2^48) 4994891777 10 Manual.Count131072.C038078.packed 64 cuts38078 = true := by
 decide +kernel
def pointBounds38078 : List (Nat × Nat × Nat) := [(4994926592,108246805075664,108247190210509)]
theorem point_links_checked38078 : (cuts38078.take 1).map (fun c => (4994891777-1+2*2^10*c.k,108246717053285+c.lower,108247102188076+c.upper)) = pointBounds38078 := by
 decide +kernel
def cuts38079 : List PrefixCut := [⟨30,157500282,157500376⟩,
⟨64,336693233,336693434⟩]
theorem checked38079 : checkPrefixCuts (2^48) 4995022849 10 Manual.Count131072.C038079.packed 64 cuts38079 = true := by
 decide +kernel
def pointBounds38079 : List (Nat × Nat × Nat) := [(4995084288,108247201055992,108247586191077)]
theorem point_links_checked38079 : (cuts38079.take 1).map (fun c => (4995022849-1+2*2^10*c.k,108247043555710+c.lower,108247428690701+c.upper)) = pointBounds38079 := by
 decide +kernel
def cuts38080 : List PrefixCut := [⟨43,221733698,221733832⟩,
⟨64,329020965,329021166⟩]
theorem checked38080 : checkPrefixCuts (2^48) 4995153921 10 Manual.Count131072.C038080.packed 64 cuts38080 = true := by
 decide +kernel
def pointBounds38080 : List (Nat × Nat × Nat) := [(4995241984,108247601982641,108247987117967)]
theorem point_links_checked38080 : (cuts38080.take 1).map (fun c => (4995153921-1+2*2^10*c.k,108247380248943+c.lower,108247765384135+c.upper)) = pointBounds38080 := by
 decide +kernel
def cuts38081 : List PrefixCut := [⟨56,292612360,292612533⟩,
⟨64,334252591,334252787⟩]
theorem checked38081 : checkPrefixCuts (2^48) 4995284993 10 Manual.Count131072.C038081.packed 64 cuts38081 = true := by
 decide +kernel
def pointBounds38081 : List (Nat × Nat × Nat) := [(4995399680,108248001882268,108248387017834)]
theorem point_links_checked38081 : (cuts38081.take 1).map (fun c => (4995284993-1+2*2^10*c.k,108247709269908+c.lower,108248094405301+c.upper)) = pointBounds38081 := by
 decide +kernel
def cuts38082 : List PrefixCut := [⟨64,328834639,328834840⟩]
theorem checked38082 : checkPrefixCuts (2^48) 4995416065 10 Manual.Count131072.C038082.packed 64 cuts38082 = true := by
 decide +kernel
def cuts38083 : List PrefixCut := [⟨5,26538543,26538558⟩,
⟨64,333389941,333390140⟩]
theorem checked38083 : checkPrefixCuts (2^48) 4995547137 10 Manual.Count131072.C038083.packed 64 cuts38083 = true := by
 decide +kernel
def pointBounds38083 : List (Nat × Nat × Nat) := [(4995557376,108248398895681,108248784031486)]
theorem point_links_checked38083 : (cuts38083.take 1).map (fun c => (4995547137-1+2*2^10*c.k,108248372357138+c.lower,108248757492928+c.upper)) = pointBounds38083 := by
 decide +kernel
def cuts38084 : List PrefixCut := [⟨18,92065224,92065278⟩,
⟨64,329775206,329775403⟩]
theorem checked38084 : checkPrefixCuts (2^48) 4995678209 10 Manual.Count131072.C038084.packed 64 cuts38084 = true := by
 decide +kernel
def pointBounds38084 : List (Nat × Nat × Nat) := [(4995715072,108248797812303,108249182948346)]
theorem point_links_checked38084 : (cuts38084.take 1).map (fun c => (4995678209-1+2*2^10*c.k,108248705747079+c.lower,108249090883068+c.upper)) = pointBounds38084 := by
 decide +kernel
def cuts38085 : List PrefixCut := [⟨31,162320843,162320945⟩,
⟨64,333428766,333428973⟩]
theorem checked38085 : checkPrefixCuts (2^48) 4995809281 10 Manual.Count131072.C038085.packed 64 cuts38085 = true := by
 decide +kernel
def pointBounds38085 : List (Nat × Nat × Nat) := [(4995872768,108249197843128,108249582979416)]
theorem point_links_checked38085 : (cuts38085.take 1).map (fun c => (4995809281-1+2*2^10*c.k,108249035522285+c.lower,108249420658471+c.upper)) = pointBounds38085 := by
 decide +kernel
def cuts38086 : List PrefixCut := [⟨44,226205952,226206091⟩,
⟨64,329025492,329025695⟩]
theorem checked38086 : checkPrefixCuts (2^48) 4995940353 10 Manual.Count131072.C038086.packed 64 cuts38086 = true := by
 decide +kernel
def pointBounds38086 : List (Nat × Nat × Nat) := [(4996030464,108249595157003,108249980293535)]
theorem point_links_checked38086 : (cuts38086.take 1).map (fun c => (4995940353-1+2*2^10*c.k,108249368951051+c.lower,108249754087444+c.upper)) = pointBounds38086 := by
 decide +kernel
def cuts38087 : List PrefixCut := [⟨57,291946560,291946735⟩,
⟨64,328566161,328566357⟩]
theorem checked38087 : checkPrefixCuts (2^48) 4996071425 10 Manual.Count131072.C038087.packed 64 cuts38087 = true := by
 decide +kernel
def pointBounds38087 : List (Nat × Nat × Nat) := [(4996188160,108249989923103,108250375059874)]
theorem point_links_checked38087 : (cuts38087.take 1).map (fun c => (4996071425-1+2*2^10*c.k,108249697976543+c.lower,108250083113139+c.upper)) = pointBounds38087 := by
 decide +kernel
def cuts38088 : List PrefixCut := [⟨64,329233580,329233778⟩]
theorem checked38088 : checkPrefixCuts (2^48) 4996202497 10 Manual.Count131072.C038088.packed 64 cuts38088 = true := by
 decide +kernel
def cuts38089 : List PrefixCut := [⟨6,31379274,31379293⟩,
⟨64,329168628,329168829⟩]
theorem checked38089 : checkPrefixCuts (2^48) 4996333569 10 Manual.Count131072.C038089.packed 64 cuts38089 = true := by
 decide +kernel
def pointBounds38089 : List (Nat × Nat × Nat) := [(4996345856,108250387155558,108250772292567)]
theorem point_links_checked38089 : (cuts38089.take 1).map (fun c => (4996333569-1+2*2^10*c.k,108250355776284+c.lower,108250740913274+c.upper)) = pointBounds38089 := by
 decide +kernel
def cuts38090 : List PrefixCut := [⟨19,96388480,96388538⟩,
⟨64,326624934,326625130⟩]
theorem checked38090 : checkPrefixCuts (2^48) 4996464641 10 Manual.Count131072.C038090.packed 64 cuts38090 = true := by
 decide +kernel
def pointBounds38090 : List (Nat × Nat × Nat) := [(4996503552,108250781333392,108251166470641)]
theorem point_links_checked38090 : (cuts38090.take 1).map (fun c => (4996464641-1+2*2^10*c.k,108250684944912+c.lower,108251070082103+c.upper)) = pointBounds38090 := by
 decide +kernel
def cuts38091 : List PrefixCut := [⟨32,166463899,166463999⟩,
⟨64,329207709,329207908⟩]
theorem checked38091 : checkPrefixCuts (2^48) 4996595713 10 Manual.Count131072.C038091.packed 64 cuts38091 = true := by
 decide +kernel
def pointBounds38091 : List (Nat × Nat × Nat) := [(4996661248,108251178033745,108251563171232)]
theorem point_links_checked38091 : (cuts38091.take 1).map (fun c => (4996595713-1+2*2^10*c.k,108251011569846+c.lower,108251396707233+c.upper)) = pointBounds38091 := by
 decide +kernel
def cuts38092 : List PrefixCut := [⟨45,231352815,231352951⟩,
⟨64,327565480,327565672⟩]
theorem checked38092 : checkPrefixCuts (2^48) 4996726785 10 Manual.Count131072.C038092.packed 64 cuts38092 = true := by
 decide +kernel
def pointBounds38092 : List (Nat × Nat × Nat) := [(4996818944,108251572130370,108251957268092)]
theorem point_links_checked38092 : (cuts38092.take 1).map (fun c => (4996726785-1+2*2^10*c.k,108251340777555+c.lower,108251725915141+c.upper)) = pointBounds38092 := by
 decide +kernel
def cuts38093 : List PrefixCut := [⟨58,297646179,297646360⟩,
⟨64,326824582,326824782⟩]
theorem checked38093 : checkPrefixCuts (2^48) 4996857857 10 Manual.Count131072.C038093.packed 64 cuts38093 = true := by
 decide +kernel
def pointBounds38093 : List (Nat × Nat × Nat) := [(4996976640,108251965989214,108252351127173)]
theorem point_links_checked38093 : (cuts38093.take 1).map (fun c => (4996857857-1+2*2^10*c.k,108251668343035+c.lower,108252053480813+c.upper)) = pointBounds38093 := by
 decide +kernel
def cuts38094 : List PrefixCut := [⟨64,324731890,324732084⟩]
theorem checked38094 : checkPrefixCuts (2^48) 4996988929 10 Manual.Count131072.C038094.packed 64 cuts38094 = true := by
 decide +kernel
def cuts38095 : List PrefixCut := [⟨7,34472334,34472353⟩,
⟨64,327708628,327708824⟩]
theorem checked38095 : checkPrefixCuts (2^48) 4997120001 10 Manual.Count131072.C038095.packed 64 cuts38095 = true := by
 decide +kernel
def pointBounds38095 : List (Nat × Nat × Nat) := [(4997134336,108252354371841,108252739510032)]
theorem point_links_checked38095 : (cuts38095.take 1).map (fun c => (4997120001-1+2*2^10*c.k,108252319899507+c.lower,108252705037679+c.upper)) = pointBounds38095 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000252
