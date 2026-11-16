import PlattAssemblyKernel
import PlattCertificates.Count131072.C068064
import PlattCertificates.Count131072.C068065
import PlattCertificates.Count131072.C068066
import PlattCertificates.Count131072.C068067
import PlattCertificates.Count131072.C068068
import PlattCertificates.Count131072.C068069
import PlattCertificates.Count131072.C068070
import PlattCertificates.Count131072.C068071
import PlattCertificates.Count131072.C068072
import PlattCertificates.Count131072.C068073
import PlattCertificates.Count131072.C068074
import PlattCertificates.Count131072.C068075
import PlattCertificates.Count131072.C068076
import PlattCertificates.Count131072.C068077
import PlattCertificates.Count131072.C068078
import PlattCertificates.Count131072.C068079
import PlattCertificates.Count131072.C068080
import PlattCertificates.Count131072.C068081
import PlattCertificates.Count131072.C068082
import PlattCertificates.Count131072.C068083
import PlattCertificates.Count131072.C068084
import PlattCertificates.Count131072.C068085
import PlattCertificates.Count131072.C068086
import PlattCertificates.Count131072.C068087
import PlattCertificates.Count131072.C068088
import PlattCertificates.Count131072.C068089
import PlattCertificates.Count131072.C068090
import PlattCertificates.Count131072.C068091
import PlattCertificates.Count131072.C068092
import PlattCertificates.Count131072.C068093
import PlattCertificates.Count131072.C068094
import PlattCertificates.Count131072.C068095
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000252
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68064 : List PrefixCut := [⟨64,177741439,177741542⟩]
theorem checked68064 : checkPrefixCuts (2^48) 8925216769 10 Manual.Count131072.C068064.packed 64 cuts68064 = true := by
 decide +kernel
def cuts68065 : List PrefixCut := [⟨41,114477233,114477300⟩,
⟨64,179441795,179441898⟩]
theorem checked68065 : checkPrefixCuts (2^48) 8925347841 10 Manual.Count131072.C068065.packed 64 cuts68065 = true := by
 decide +kernel
def pointBounds68065 : List (Nat × Nat × Nat) := [(8925431808,115469838082992,115470227386480)]
theorem point_links_checked68065 : (cuts68065.take 1).map (fun c => (8925347841-1+2*2^10*c.k,115469723605759+c.lower,115470112909180+c.upper)) = pointBounds68065 := by
 decide +kernel
def cuts68066 : List PrefixCut := [⟨64,180227556,180227658⟩]
theorem checked68066 : checkPrefixCuts (2^48) 8925478913 10 Manual.Count131072.C068066.packed 64 cuts68066 = true := by
 decide +kernel
def cuts68067 : List PrefixCut := [⟨50,141436580,141436658⟩,
⟨64,180824088,180824190⟩]
theorem checked68067 : checkPrefixCuts (2^48) 8925609985 10 Manual.Count131072.C068067.packed 64 cuts68067 = true := by
 decide +kernel
def pointBounds68067 : List (Nat × Nat × Nat) := [(8925712384,115470224711690,115470614015394)]
theorem point_links_checked68067 : (cuts68067.take 1).map (fun c => (8925609985-1+2*2^10*c.k,115470083275110+c.lower,115470472578736+c.upper)) = pointBounds68067 := by
 decide +kernel
def cuts68068 : List PrefixCut := [⟨64,181578260,181578368⟩]
theorem checked68068 : checkPrefixCuts (2^48) 8925741057 10 Manual.Count131072.C068068.packed 64 cuts68068 = true := by
 decide +kernel
def cuts68069 : List PrefixCut := [⟨59,166407593,166407685⟩,
⟨64,180534949,180535050⟩]
theorem checked68069 : checkPrefixCuts (2^48) 8925872129 10 Manual.Count131072.C068069.packed 64 cuts68069 = true := by
 decide +kernel
def pointBounds68069 : List (Nat × Nat × Nat) := [(8925992960,115470612085051,115471001388979)]
theorem point_links_checked68069 : (cuts68069.take 1).map (fun c => (8925872129-1+2*2^10*c.k,115470445677458+c.lower,115470834981294+c.upper)) = pointBounds68069 := by
 decide +kernel
def cuts68070 : List PrefixCut := [⟨64,180658436,180658543⟩]
theorem checked68070 : checkPrefixCuts (2^48) 8926003201 10 Manual.Count131072.C068070.packed 64 cuts68070 = true := by
 decide +kernel
def cuts68071 : List PrefixCut := [⟨64,179457523,179457626⟩]
theorem checked68071 : checkPrefixCuts (2^48) 8926134273 10 Manual.Count131072.C068071.packed 64 cuts68071 = true := by
 decide +kernel
def cuts68072 : List PrefixCut := [⟨4,11036662,11036667⟩,
⟨64,180463928,180464033⟩]
theorem checked68072 : checkPrefixCuts (2^48) 8926265345 10 Manual.Count131072.C068072.packed 64 cuts68072 = true := by
 decide +kernel
def pointBounds68072 : List (Nat × Nat × Nat) := [(8926273536,115470997365028,115471386669180)]
theorem point_links_checked68072 : (cuts68072.take 1).map (fun c => (8926265345-1+2*2^10*c.k,115470986328366+c.lower,115471375632513+c.upper)) = pointBounds68072 := by
 decide +kernel
def cuts68073 : List PrefixCut := [⟨64,182920836,182920945⟩]
theorem checked68073 : checkPrefixCuts (2^48) 8926396417 10 Manual.Count131072.C068073.packed 64 cuts68073 = true := by
 decide +kernel
def cuts68074 : List PrefixCut := [⟨13,36388343,36388364⟩,
⟨64,181499197,181499303⟩]
theorem checked68074 : checkPrefixCuts (2^48) 8926527489 10 Manual.Count131072.C068074.packed 64 cuts68074 = true := by
 decide +kernel
def pointBounds68074 : List (Nat × Nat × Nat) := [(8926554112,115471386101473,115471775405855)]
theorem point_links_checked68074 : (cuts68074.take 1).map (fun c => (8926527489-1+2*2^10*c.k,115471349713130+c.lower,115471739017491+c.upper)) = pointBounds68074 := by
 decide +kernel
def cuts68075 : List PrefixCut := [⟨64,180424456,180424557⟩]
theorem checked68075 : checkPrefixCuts (2^48) 8926658561 10 Manual.Count131072.C068075.packed 64 cuts68075 = true := by
 decide +kernel
def cuts68076 : List PrefixCut := [⟨22,61423170,61423205⟩,
⟨64,179412809,179412912⟩]
theorem checked68076 : checkPrefixCuts (2^48) 8926789633 10 Manual.Count131072.C068076.packed 64 cuts68076 = true := by
 decide +kernel
def pointBounds68076 : List (Nat × Nat × Nat) := [(8926834688,115471773059953,115472162364556)]
theorem point_links_checked68076 : (cuts68076.take 1).map (fun c => (8926789633-1+2*2^10*c.k,115471711636783+c.lower,115472100941351+c.upper)) = pointBounds68076 := by
 decide +kernel
def cuts68077 : List PrefixCut := [⟨64,181869576,181869680⟩]
theorem checked68077 : checkPrefixCuts (2^48) 8926920705 10 Manual.Count131072.C068077.packed 64 cuts68077 = true := by
 decide +kernel
def cuts68078 : List PrefixCut := [⟨31,86204231,86204282⟩,
⟨64,182150664,182150770⟩]
theorem checked68078 : checkPrefixCuts (2^48) 8927051777 10 Manual.Count131072.C068078.packed 64 cuts68078 = true := by
 decide +kernel
def pointBounds68078 : List (Nat × Nat × Nat) := [(8927115264,115472159123399,115472548428225)]
theorem point_links_checked68078 : (cuts68078.take 1).map (fun c => (8927051777-1+2*2^10*c.k,115472072919168+c.lower,115472462223943+c.upper)) = pointBounds68078 := by
 decide +kernel
def cuts68079 : List PrefixCut := [⟨64,179720200,179720302⟩]
theorem checked68079 : checkPrefixCuts (2^48) 8927182849 10 Manual.Count131072.C068079.packed 64 cuts68079 = true := by
 decide +kernel
def cuts68080 : List PrefixCut := [⟨40,113096259,113096327⟩,
⟨64,180222040,180222148⟩]
theorem checked68080 : checkPrefixCuts (2^48) 8927313921 10 Manual.Count131072.C068080.packed 64 cuts68080 = true := by
 decide +kernel
def pointBounds68080 : List (Nat × Nat × Nat) := [(8927395840,115472547886291,115472937191342)]
theorem point_links_checked68080 : (cuts68080.take 1).map (fun c => (8927313921-1+2*2^10*c.k,115472434790032+c.lower,115472824095015+c.upper)) = pointBounds68080 := by
 decide +kernel
def cuts68081 : List PrefixCut := [⟨64,181291365,181291472⟩]
theorem checked68081 : checkPrefixCuts (2^48) 8927444993 10 Manual.Count131072.C068081.packed 64 cuts68081 = true := by
 decide +kernel
def cuts68082 : List PrefixCut := [⟨49,138378704,138378788⟩,
⟨64,181131072,181131180⟩]
theorem checked68082 : checkPrefixCuts (2^48) 8927576065 10 Manual.Count131072.C068082.packed 64 cuts68082 = true := by
 decide +kernel
def pointBounds68082 : List (Nat × Nat × Nat) := [(8927676416,115472934682141,115473323987423)]
theorem point_links_checked68082 : (cuts68082.take 1).map (fun c => (8927576065-1+2*2^10*c.k,115472796303437+c.lower,115473185608635+c.upper)) = pointBounds68082 := by
 decide +kernel
def cuts68083 : List PrefixCut := [⟨64,178101724,178101832⟩]
theorem checked68083 : checkPrefixCuts (2^48) 8927707137 10 Manual.Count131072.C068083.packed 64 cuts68083 = true := by
 decide +kernel
def cuts68084 : List PrefixCut := [⟨58,165267505,165267601⟩,
⟨64,181945466,181945571⟩]
theorem checked68084 : checkPrefixCuts (2^48) 8927838209 10 Manual.Count131072.C068084.packed 64 cuts68084 = true := by
 decide +kernel
def pointBounds68084 : List (Nat × Nat × Nat) := [(8927956992,115473320803738,115473710109248)]
theorem point_links_checked68084 : (cuts68084.take 1).map (fun c => (8927838209-1+2*2^10*c.k,115473155536233+c.lower,115473544841647+c.upper)) = pointBounds68084 := by
 decide +kernel
def cuts68085 : List PrefixCut := [⟨64,182068913,182069017⟩]
theorem checked68085 : checkPrefixCuts (2^48) 8927969281 10 Manual.Count131072.C068085.packed 64 cuts68085 = true := by
 decide +kernel
def cuts68086 : List PrefixCut := [⟨64,181372635,181372744⟩]
theorem checked68086 : checkPrefixCuts (2^48) 8928100353 10 Manual.Count131072.C068086.packed 64 cuts68086 = true := by
 decide +kernel
def cuts68087 : List PrefixCut := [⟨3,7881594,7881599⟩,
⟨64,180581826,180581933⟩]
theorem checked68087 : checkPrefixCuts (2^48) 8928231425 10 Manual.Count131072.C068087.packed 64 cuts68087 = true := by
 decide +kernel
def pointBounds68087 : List (Nat × Nat × Nat) := [(8928237568,115473708804841,115474098110578)]
theorem point_links_checked68087 : (cuts68087.take 1).map (fun c => (8928231425-1+2*2^10*c.k,115473700923247+c.lower,115474090228979+c.upper)) = pointBounds68087 := by
 decide +kernel
def cuts68088 : List PrefixCut := [⟨64,178593052,178593154⟩]
theorem checked68088 : checkPrefixCuts (2^48) 8928362497 10 Manual.Count131072.C068088.packed 64 cuts68088 = true := by
 decide +kernel
def cuts68089 : List PrefixCut := [⟨12,32691859,32691879⟩,
⟨64,177896881,177896985⟩]
theorem checked68089 : checkPrefixCuts (2^48) 8928493569 10 Manual.Count131072.C068089.packed 64 cuts68089 = true := by
 decide +kernel
def pointBounds68089 : List (Nat × Nat × Nat) := [(8928518144,115474092789984,115474482095945)]
theorem point_links_checked68089 : (cuts68089.take 1).map (fun c => (8928493569-1+2*2^10*c.k,115474060098125+c.lower,115474449404066+c.upper)) = pointBounds68089 := by
 decide +kernel
def cuts68090 : List PrefixCut := [⟨64,182150120,182150231⟩]
theorem checked68090 : checkPrefixCuts (2^48) 8928624641 10 Manual.Count131072.C068090.packed 64 cuts68090 = true := by
 decide +kernel
def cuts68091 : List PrefixCut := [⟨21,58068059,58068090⟩,
⟨64,179121102,179121208⟩]
theorem checked68091 : checkPrefixCuts (2^48) 8928755713 10 Manual.Count131072.C068091.packed 64 cuts68091 = true := by
 decide +kernel
def pointBounds68091 : List (Nat × Nat × Nat) := [(8928798720,115474478213185,115474867519372)]
theorem point_links_checked68091 : (cuts68091.take 1).map (fun c => (8928755713-1+2*2^10*c.k,115474420145126+c.lower,115474809451282+c.upper)) = pointBounds68091 := by
 decide +kernel
def cuts68092 : List PrefixCut := [⟨64,178834764,178834866⟩]
theorem checked68092 : checkPrefixCuts (2^48) 8928886785 10 Manual.Count131072.C068092.packed 64 cuts68092 = true := by
 decide +kernel
def cuts68093 : List PrefixCut := [⟨30,82906820,82906867⟩,
⟨64,178674523,178674624⟩]
theorem checked68093 : checkPrefixCuts (2^48) 8929017857 10 Manual.Count131072.C068093.packed 64 cuts68093 = true := by
 decide +kernel
def pointBounds68093 : List (Nat × Nat × Nat) := [(8929079296,115474861007812,115475250314223)]
theorem point_links_checked68093 : (cuts68093.take 1).map (fun c => (8929017857-1+2*2^10*c.k,115474778100992+c.lower,115475167407356+c.upper)) = pointBounds68093 := by
 decide +kernel
def cuts68094 : List PrefixCut := [⟨64,183999278,183999386⟩]
theorem checked68094 : checkPrefixCuts (2^48) 8929148929 10 Manual.Count131072.C068094.packed 64 cuts68094 = true := by
 decide +kernel
def cuts68095 : List PrefixCut := [⟨39,111337627,111337696⟩,
⟨64,183208502,183208614⟩]
theorem checked68095 : checkPrefixCuts (2^48) 8929280001 10 Manual.Count131072.C068095.packed 64 cuts68095 = true := by
 decide +kernel
def pointBounds68095 : List (Nat × Nat × Nat) := [(8929359872,115475252112420,115475641419062)]
theorem point_links_checked68095 : (cuts68095.take 1).map (fun c => (8929280001-1+2*2^10*c.k,115475140774793+c.lower,115475530081366+c.upper)) = pointBounds68095 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000252
