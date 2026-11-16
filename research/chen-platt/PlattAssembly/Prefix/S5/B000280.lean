import PlattAssemblyKernel
import PlattCertificates.Count131072.C048960
import PlattCertificates.Count131072.C048961
import PlattCertificates.Count131072.C048962
import PlattCertificates.Count131072.C048963
import PlattCertificates.Count131072.C048964
import PlattCertificates.Count131072.C048965
import PlattCertificates.Count131072.C048966
import PlattCertificates.Count131072.C048967
import PlattCertificates.Count131072.C048968
import PlattCertificates.Count131072.C048969
import PlattCertificates.Count131072.C048970
import PlattCertificates.Count131072.C048971
import PlattCertificates.Count131072.C048972
import PlattCertificates.Count131072.C048973
import PlattCertificates.Count131072.C048974
import PlattCertificates.Count131072.C048975
import PlattCertificates.Count131072.C048976
import PlattCertificates.Count131072.C048977
import PlattCertificates.Count131072.C048978
import PlattCertificates.Count131072.C048979
import PlattCertificates.Count131072.C048980
import PlattCertificates.Count131072.C048981
import PlattCertificates.Count131072.C048982
import PlattCertificates.Count131072.C048983
import PlattCertificates.Count131072.C048984
import PlattCertificates.Count131072.C048985
import PlattCertificates.Count131072.C048986
import PlattCertificates.Count131072.C048987
import PlattCertificates.Count131072.C048988
import PlattCertificates.Count131072.C048989
import PlattCertificates.Count131072.C048990
import PlattCertificates.Count131072.C048991
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000280
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48960 : List PrefixCut := [⟨64,251698758,251698899⟩]
theorem checked48960 : checkPrefixCuts (2^48) 6421217281 10 Manual.Count131072.C048960.packed 64 cuts48960 = true := by
 decide +kernel
def cuts48961 : List PrefixCut := [⟨26,104325042,104325104⟩,
⟨64,255419474,255419621⟩]
theorem checked48961 : checkPrefixCuts (2^48) 6421348353 10 Manual.Count131072.C048961.packed 64 cuts48961 = true := by
 decide +kernel
def pointBounds48961 : List (Nat × Nat × Nat) := [(6421401600,111395481465037,111395868438130)]
theorem point_links_checked48961 : (cuts48961.take 1).map (fun c => (6421348353-1+2*2^10*c.k,111395377139995+c.lower,111395764113026+c.upper)) = pointBounds48961 := by
 decide +kernel
def cuts48962 : List PrefixCut := [⟨60,238757939,238758074⟩,
⟨64,255282783,255282927⟩]
theorem checked48962 : checkPrefixCuts (2^48) 6421479425 10 Manual.Count131072.C048962.packed 64 cuts48962 = true := by
 decide +kernel
def pointBounds48962 : List (Nat × Nat × Nat) := [(6421602304,111395871317408,111396258290721)]
theorem point_links_checked48962 : (cuts48962.take 1).map (fun c => (6421479425-1+2*2^10*c.k,111395632559469+c.lower,111396019532647+c.upper)) = pointBounds48962 := by
 decide +kernel
def cuts48963 : List PrefixCut := [⟨64,252077822,252077964⟩]
theorem checked48963 : checkPrefixCuts (2^48) 6421610497 10 Manual.Count131072.C048963.packed 64 cuts48963 = true := by
 decide +kernel
def cuts48964 : List PrefixCut := [⟨30,119878721,119878785⟩,
⟨64,256543443,256543591⟩]
theorem checked48964 : checkPrefixCuts (2^48) 6421741569 10 Manual.Count131072.C048964.packed 64 cuts48964 = true := by
 decide +kernel
def pointBounds48964 : List (Nat × Nat × Nat) := [(6421803008,111396259798795,111396646772323)]
theorem point_links_checked48964 : (cuts48964.take 1).map (fun c => (6421741569-1+2*2^10*c.k,111396139920074+c.lower,111396526893538+c.upper)) = pointBounds48964 := by
 decide +kernel
def cuts48965 : List PrefixCut := [⟨64,254434386,254434532⟩]
theorem checked48965 : checkPrefixCuts (2^48) 6421872641 10 Manual.Count131072.C048965.packed 64 cuts48965 = true := by
 decide +kernel
def pointBounds48965 : List (Nat × Nat × Nat) := [(6422003712,111396650897903,111397037871661)]
theorem point_links_checked48965 : (cuts48965.take 1).map (fun c => (6421872641-1+2*2^10*c.k,111396396463517+c.lower,111396783437129+c.upper)) = pointBounds48965 := by
 decide +kernel
def cuts48966 : List PrefixCut := [⟨64,253333426,253333572⟩]
theorem checked48966 : checkPrefixCuts (2^48) 6422003713 10 Manual.Count131072.C048966.packed 64 cuts48966 = true := by
 decide +kernel
def cuts48967 : List PrefixCut := [⟨34,135605789,135605864⟩,
⟨64,253109147,253109289⟩]
theorem checked48967 : checkPrefixCuts (2^48) 6422134785 10 Manual.Count131072.C048967.packed 64 cuts48967 = true := by
 decide +kernel
def pointBounds48967 : List (Nat × Nat × Nat) := [(6422204416,111397039837118,111397426811097)]
theorem point_links_checked48967 : (cuts48967.take 1).map (fun c => (6422134785-1+2*2^10*c.k,111396904231329+c.lower,111397291205233+c.upper)) = pointBounds48967 := by
 decide +kernel
def cuts48968 : List PrefixCut := [⟨64,255032366,255032514⟩]
theorem checked48968 : checkPrefixCuts (2^48) 6422265857 10 Manual.Count131072.C048968.packed 64 cuts48968 = true := by
 decide +kernel
def cuts48969 : List PrefixCut := [⟨4,15777739,15777747⟩,
⟨64,254282109,254282253⟩]
theorem checked48969 : checkPrefixCuts (2^48) 6422396929 10 Manual.Count131072.C048969.packed 64 cuts48969 = true := by
 decide +kernel
def pointBounds48969 : List (Nat × Nat × Nat) := [(6422405120,111397428150581,111397815124783)]
theorem point_links_checked48969 : (cuts48969.take 1).map (fun c => (6422396929-1+2*2^10*c.k,111397412372842+c.lower,111397799347036+c.upper)) = pointBounds48969 := by
 decide +kernel
def cuts48970 : List PrefixCut := [⟨38,150673507,150673593⟩,
⟨64,255591689,255591837⟩]
theorem checked48970 : checkPrefixCuts (2^48) 6422528001 10 Manual.Count131072.C048970.packed 64 cuts48970 = true := by
 decide +kernel
def pointBounds48970 : List (Nat × Nat × Nat) := [(6422605824,111397817328458,111398204302882)]
theorem point_links_checked48970 : (cuts48970.take 1).map (fun c => (6422528001-1+2*2^10*c.k,111397666654951+c.lower,111398053629289+c.upper)) = pointBounds48970 := by
 decide +kernel
def cuts48971 : List PrefixCut := [⟨64,254929103,254929244⟩]
theorem checked48971 : checkPrefixCuts (2^48) 6422659073 10 Manual.Count131072.C048971.packed 64 cuts48971 = true := by
 decide +kernel
def cuts48972 : List PrefixCut := [⟨9,35760656,35760675⟩,
⟨64,253390062,253390203⟩]
theorem checked48972 : checkPrefixCuts (2^48) 6422790145 10 Manual.Count131072.C048972.packed 64 cuts48972 = true := by
 decide +kernel
def pointBounds48972 : List (Nat × Nat × Nat) := [(6422808576,111398212936399,111398599911045)]
theorem point_links_checked48972 : (cuts48972.take 1).map (fun c => (6422790145-1+2*2^10*c.k,111398177175743+c.lower,111398564150370+c.upper)) = pointBounds48972 := by
 decide +kernel
def cuts48973 : List PrefixCut := [⟨44,173364549,173364644⟩,
⟨64,254217515,254217654⟩]
theorem checked48973 : checkPrefixCuts (2^48) 6422921217 10 Manual.Count131072.C048973.packed 64 cuts48973 = true := by
 decide +kernel
def pointBounds48973 : List (Nat × Nat × Nat) := [(6423011328,111398603930354,111398990905217)]
theorem point_links_checked48973 : (cuts48973.take 1).map (fun c => (6422921217-1+2*2^10*c.k,111398430565805+c.lower,111398817540573+c.upper)) = pointBounds48973 := by
 decide +kernel
def cuts48974 : List PrefixCut := [⟨64,258068710,258068856⟩]
theorem checked48974 : checkPrefixCuts (2^48) 6423052289 10 Manual.Count131072.C048974.packed 64 cuts48974 = true := by
 decide +kernel
def cuts48975 : List PrefixCut := [⟨15,59860318,59860349⟩,
⟨64,255434157,255434302⟩]
theorem checked48975 : checkPrefixCuts (2^48) 6423183361 10 Manual.Count131072.C048975.packed 64 cuts48975 = true := by
 decide +kernel
def pointBounds48975 : List (Nat × Nat × Nat) := [(6423214080,111399002712348,111399389687432)]
theorem point_links_checked48975 : (cuts48975.take 1).map (fun c => (6423183361-1+2*2^10*c.k,111398942852030+c.lower,111399329827083+c.upper)) = pointBounds48975 := by
 decide +kernel
def cuts48976 : List PrefixCut := [⟨50,195307826,195307940⟩,
⟨64,251835654,251835799⟩]
theorem checked48976 : checkPrefixCuts (2^48) 6423314433 10 Manual.Count131072.C048976.packed 64 cuts48976 = true := by
 decide +kernel
def pointBounds48976 : List (Nat × Nat × Nat) := [(6423416832,111399393594013,111399780569325)]
theorem point_links_checked48976 : (cuts48976.take 1).map (fun c => (6423314433-1+2*2^10*c.k,111399198286187+c.lower,111399585261385+c.upper)) = pointBounds48976 := by
 decide +kernel
def cuts48977 : List PrefixCut := [⟨64,252268730,252268880⟩]
theorem checked48977 : checkPrefixCuts (2^48) 6423445505 10 Manual.Count131072.C048977.packed 64 cuts48977 = true := by
 decide +kernel
def cuts48978 : List PrefixCut := [⟨21,83387335,83387381⟩,
⟨64,254103965,254104105⟩]
theorem checked48978 : checkPrefixCuts (2^48) 6423576577 10 Manual.Count131072.C048978.packed 64 cuts48978 = true := by
 decide +kernel
def pointBounds48978 : List (Nat × Nat × Nat) := [(6423619584,111399785777906,111400172753445)]
theorem point_links_checked48978 : (cuts48978.take 1).map (fun c => (6423576577-1+2*2^10*c.k,111399702390571+c.lower,111400089366064+c.upper)) = pointBounds48978 := by
 decide +kernel
def cuts48979 : List PrefixCut := [⟨56,222243606,222243728⟩,
⟨64,254712224,254712365⟩]
theorem checked48979 : checkPrefixCuts (2^48) 6423707649 10 Manual.Count131072.C048979.packed 64 cuts48979 = true := by
 decide +kernel
def pointBounds48979 : List (Nat × Nat × Nat) := [(6423822336,111400178738142,111400565713897)]
theorem point_links_checked48979 : (cuts48979.take 1).map (fun c => (6423707649-1+2*2^10*c.k,111399956494536+c.lower,111400343470169+c.upper)) = pointBounds48979 := by
 decide +kernel
def cuts48980 : List PrefixCut := [⟨64,255758623,255758770⟩]
theorem checked48980 : checkPrefixCuts (2^48) 6423838721 10 Manual.Count131072.C048980.packed 64 cuts48980 = true := by
 decide +kernel
def cuts48981 : List PrefixCut := [⟨27,107305773,107305834⟩,
⟨64,255534324,255534471⟩]
theorem checked48981 : checkPrefixCuts (2^48) 6423969793 10 Manual.Count131072.C048981.packed 64 cuts48981 = true := by
 decide +kernel
def pointBounds48981 : List (Nat × Nat × Nat) := [(6424025088,111400574271156,111400961247138)]
theorem point_links_checked48981 : (cuts48981.take 1).map (fun c => (6423969793-1+2*2^10*c.k,111400466965383+c.lower,111400853941304+c.upper)) = pointBounds48981 := by
 decide +kernel
def cuts48982 : List PrefixCut := [⟨62,246678552,246678693⟩,
⟨64,254477547,254477692⟩]
theorem checked48982 : checkPrefixCuts (2^48) 6424100865 10 Manual.Count131072.C048982.packed 64 cuts48982 = true := by
 decide +kernel
def pointBounds48982 : List (Nat × Nat × Nat) := [(6424227840,111400969178259,111401356154468)]
theorem point_links_checked48982 : (cuts48982.take 1).map (fun c => (6424100865-1+2*2^10*c.k,111400722499707+c.lower,111401109475775+c.upper)) = pointBounds48982 := by
 decide +kernel
def cuts48983 : List PrefixCut := [⟨64,255480091,255480241⟩]
theorem checked48983 : checkPrefixCuts (2^48) 6424231937 10 Manual.Count131072.C048983.packed 64 cuts48983 = true := by
 decide +kernel
def cuts48984 : List PrefixCut := [⟨33,132097510,132097590⟩,
⟨64,252539414,252539560⟩]
theorem checked48984 : checkPrefixCuts (2^48) 6424363009 10 Manual.Count131072.C048984.packed 64 cuts48984 = true := by
 decide +kernel
def pointBounds48984 : List (Nat × Nat × Nat) := [(6424430592,111401364554855,111401751531298)]
theorem point_links_checked48984 : (cuts48984.take 1).map (fun c => (6424363009-1+2*2^10*c.k,111401232457345+c.lower,111401619433708+c.upper)) = pointBounds48984 := by
 decide +kernel
def cuts48985 : List PrefixCut := [⟨64,256039252,256039403⟩]
theorem checked48985 : checkPrefixCuts (2^48) 6424494081 10 Manual.Count131072.C048985.packed 64 cuts48985 = true := by
 decide +kernel
def cuts48986 : List PrefixCut := [⟨4,15246524,15246532⟩,
⟨64,252397656,252397800⟩]
theorem checked48986 : checkPrefixCuts (2^48) 6424625153 10 Manual.Count131072.C048986.packed 64 cuts48986 = true := by
 decide +kernel
def pointBounds48986 : List (Nat × Nat × Nat) := [(6424633344,111401756282535,111402143259203)]
theorem point_links_checked48986 : (cuts48986.take 1).map (fun c => (6424625153-1+2*2^10*c.k,111401741036011+c.lower,111402128012671+c.upper)) = pointBounds48986 := by
 decide +kernel
def cuts48987 : List PrefixCut := [⟨39,158156670,158156762⟩,
⟨64,255853562,255853708⟩]
theorem checked48987 : checkPrefixCuts (2^48) 6424756225 10 Manual.Count131072.C048987.packed 64 cuts48987 = true := by
 decide +kernel
def pointBounds48987 : List (Nat × Nat × Nat) := [(6424836096,111402151590337,111402538567233)]
theorem point_links_checked48987 : (cuts48987.take 1).map (fun c => (6424756225-1+2*2^10*c.k,111401993433667+c.lower,111402380410471+c.upper)) = pointBounds48987 := by
 decide +kernel
def cuts48988 : List PrefixCut := [⟨64,253132123,253132269⟩]
theorem checked48988 : checkPrefixCuts (2^48) 6424887297 10 Manual.Count131072.C048988.packed 64 cuts48988 = true := by
 decide +kernel
def cuts48989 : List PrefixCut := [⟨10,38814887,38814908⟩,
⟨64,254046955,254047094⟩]
theorem checked48989 : checkPrefixCuts (2^48) 6425018369 10 Manual.Count131072.C048989.packed 64 cuts48989 = true := by
 decide +kernel
def pointBounds48989 : List (Nat × Nat × Nat) := [(6425038848,111402541234239,111402928211356)]
theorem point_links_checked48989 : (cuts48989.take 1).map (fun c => (6425018369-1+2*2^10*c.k,111402502419352+c.lower,111402889396448+c.upper)) = pointBounds48989 := by
 decide +kernel
def cuts48990 : List PrefixCut := [⟨45,180313685,180313788⟩,
⟨64,256582616,256582762⟩]
theorem checked48990 : checkPrefixCuts (2^48) 6425149441 10 Manual.Count131072.C048990.packed 64 cuts48990 = true := by
 decide +kernel
def pointBounds48990 : List (Nat × Nat × Nat) := [(6425241600,111402936779992,111403323757330)]
theorem point_links_checked48990 : (cuts48990.take 1).map (fun c => (6425149441-1+2*2^10*c.k,111402756466307+c.lower,111403143443542+c.upper)) = pointBounds48990 := by
 decide +kernel
def cuts48991 : List PrefixCut := [⟨64,256051698,256051841⟩]
theorem checked48991 : checkPrefixCuts (2^48) 6425280513 10 Manual.Count131072.C048991.packed 64 cuts48991 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000280
