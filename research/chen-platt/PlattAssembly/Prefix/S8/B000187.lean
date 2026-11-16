import PlattAssemblyKernel
import PlattCertificates.Count131072.C075984
import PlattCertificates.Count131072.C075985
import PlattCertificates.Count131072.C075986
import PlattCertificates.Count131072.C075987
import PlattCertificates.Count131072.C075988
import PlattCertificates.Count131072.C075989
import PlattCertificates.Count131072.C075990
import PlattCertificates.Count131072.C075991
import PlattCertificates.Count131072.C075992
import PlattCertificates.Count131072.C075993
import PlattCertificates.Count131072.C075994
import PlattCertificates.Count131072.C075995
import PlattCertificates.Count131072.C075996
import PlattCertificates.Count131072.C075997
import PlattCertificates.Count131072.C075998
import PlattCertificates.Count131072.C075999
import PlattCertificates.Count131072.C076000
import PlattCertificates.Count131072.C076001
import PlattCertificates.Count131072.C076002
import PlattCertificates.Count131072.C076003
import PlattCertificates.Count131072.C076004
import PlattCertificates.Count131072.C076005
import PlattCertificates.Count131072.C076006
import PlattCertificates.Count131072.C076007
import PlattCertificates.Count131072.C076008
import PlattCertificates.Count131072.C076009
import PlattCertificates.Count131072.C076010
import PlattCertificates.Count131072.C076011
import PlattCertificates.Count131072.C076012
import PlattCertificates.Count131072.C076013
import PlattCertificates.Count131072.C076014
import PlattCertificates.Count131072.C076015
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000187
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75984 : List PrefixCut := [⟨64,160606727,160606833⟩]
theorem checked75984 : checkPrefixCuts (2^48) 9963307009 10 Manual.Count131072.C075984.packed 64 cuts75984 = true := by
 decide +kernel
def cuts75985 : List PrefixCut := [⟨64,159785348,159785447⟩]
theorem checked75985 : checkPrefixCuts (2^48) 9963438081 10 Manual.Count131072.C075985.packed 64 cuts75985 = true := by
 decide +kernel
def cuts75986 : List PrefixCut := [⟨9,21950547,21950560⟩,
⟨64,161139261,161139354⟩]
theorem checked75986 : checkPrefixCuts (2^48) 9963569153 10 Manual.Count131072.C075986.packed 64 cuts75986 = true := by
 decide +kernel
def pointBounds75986 : List (Nat × Nat × Nat) := [(9963587584,116818414138226,116818804241633)]
theorem point_links_checked75986 : (cuts75986.take 1).map (fun c => (9963569153-1+2*2^10*c.k,116818392187679+c.lower,116818782291073+c.upper)) = pointBounds75986 := by
 decide +kernel
def cuts75987 : List PrefixCut := [⟨64,161532627,161532729⟩]
theorem checked75987 : checkPrefixCuts (2^48) 9963700225 10 Manual.Count131072.C075987.packed 64 cuts75987 = true := by
 decide +kernel
def cuts75988 : List PrefixCut := [⟨34,86245921,86245974⟩,
⟨64,160202794,160202893⟩]
theorem checked75988 : checkPrefixCuts (2^48) 9963831297 10 Manual.Count131072.C075988.packed 64 cuts75988 = true := by
 decide +kernel
def pointBounds75988 : List (Nat × Nat × Nat) := [(9963900928,116818801105488,116819191209130)]
theorem point_links_checked75988 : (cuts75988.take 1).map (fun c => (9963831297-1+2*2^10*c.k,116818714859567+c.lower,116819104963156+c.upper)) = pointBounds75988 := by
 decide +kernel
def cuts75989 : List PrefixCut := [⟨64,161556645,161556738⟩]
theorem checked75989 : checkPrefixCuts (2^48) 9963962369 10 Manual.Count131072.C075989.packed 64 cuts75989 = true := by
 decide +kernel
def cuts75990 : List PrefixCut := [⟨59,145396314,145396406⟩,
⟨64,158079919,158080019⟩]
theorem checked75990 : checkPrefixCuts (2^48) 9964093441 10 Manual.Count131072.C075990.packed 64 cuts75990 = true := by
 decide +kernel
def pointBounds75990 : List (Nat × Nat × Nat) := [(9964214272,116819182015320,116819572119193)]
theorem point_links_checked75990 : (cuts75990.take 1).map (fun c => (9964093441-1+2*2^10*c.k,116819036619006+c.lower,116819426722787+c.upper)) = pointBounds75990 := by
 decide +kernel
def cuts75991 : List PrefixCut := [⟨64,158755805,158755894⟩]
theorem checked75991 : checkPrefixCuts (2^48) 9964224513 10 Manual.Count131072.C075991.packed 64 cuts75991 = true := by
 decide +kernel
def cuts75992 : List PrefixCut := [⟨64,162595451,162595541⟩]
theorem checked75992 : checkPrefixCuts (2^48) 9964355585 10 Manual.Count131072.C075992.packed 64 cuts75992 = true := by
 decide +kernel
def cuts75993 : List PrefixCut := [⟨20,49744287,49744319⟩,
⟨64,159373083,159373177⟩]
theorem checked75993 : checkPrefixCuts (2^48) 9964486657 10 Manual.Count131072.C075993.packed 64 cuts75993 = true := by
 decide +kernel
def pointBounds75993 : List (Nat × Nat × Nat) := [(9964527616,116819565794468,116819955898560)]
theorem point_links_checked75993 : (cuts75993.take 1).map (fun c => (9964486657-1+2*2^10*c.k,116819516050181+c.lower,116819906154241+c.upper)) = pointBounds75993 := by
 decide +kernel
def cuts75994 : List PrefixCut := [⟨64,162026224,162026321⟩]
theorem checked75994 : checkPrefixCuts (2^48) 9964617729 10 Manual.Count131072.C075994.packed 64 cuts75994 = true := by
 decide +kernel
def cuts75995 : List PrefixCut := [⟨45,115868916,115868979⟩,
⟨64,163097478,163097569⟩]
theorem checked75995 : checkPrefixCuts (2^48) 9964748801 10 Manual.Count131072.C075995.packed 64 cuts75995 = true := by
 decide +kernel
def pointBounds75995 : List (Nat × Nat × Nat) := [(9964840960,116819953318404,116820343422718)]
theorem point_links_checked75995 : (cuts75995.take 1).map (fun c => (9964748801-1+2*2^10*c.k,116819837449488+c.lower,116820227553739+c.upper)) = pointBounds75995 := by
 decide +kernel
def cuts75996 : List PrefixCut := [⟨64,162078453,162078548⟩]
theorem checked75996 : checkPrefixCuts (2^48) 9964879873 10 Manual.Count131072.C075996.packed 64 cuts75996 = true := by
 decide +kernel
def cuts75997 : List PrefixCut := [⟨64,158602054,158602146⟩]
theorem checked75997 : checkPrefixCuts (2^48) 9965010945 10 Manual.Count131072.C075997.packed 64 cuts75997 = true := by
 decide +kernel
def cuts75998 : List PrefixCut := [⟨6,14574900,14574910⟩,
⟨64,162300149,162300248⟩]
theorem checked75998 : checkPrefixCuts (2^48) 9965142017 10 Manual.Count131072.C075998.packed 64 cuts75998 = true := by
 decide +kernel
def pointBounds75998 : List (Nat × Nat × Nat) := [(9965154304,116820335802373,116820725906912)]
theorem point_links_checked75998 : (cuts75998.take 1).map (fun c => (9965142017-1+2*2^10*c.k,116820321227473+c.lower,116820711332002+c.upper)) = pointBounds75998 := by
 decide +kernel
def cuts75999 : List PrefixCut := [⟨64,164331692,164331790⟩]
theorem checked75999 : checkPrefixCuts (2^48) 9965273089 10 Manual.Count131072.C075999.packed 64 cuts75999 = true := by
 decide +kernel
def cuts76000 : List PrefixCut := [⟨31,77335127,77335175⟩,
⟨64,160770650,160770746⟩]
theorem checked76000 : checkPrefixCuts (2^48) 9965404161 10 Manual.Count131072.C076000.packed 64 cuts76000 = true := by
 decide +kernel
def pointBounds76000 : List (Nat × Nat × Nat) := [(9965467648,116820725194441,116821115299215)]
theorem point_links_checked76000 : (cuts76000.take 1).map (fun c => (9965404161-1+2*2^10*c.k,116820647859314+c.lower,116821037964040+c.upper)) = pointBounds76000 := by
 decide +kernel
def cuts76001 : List PrefixCut := [⟨64,159610512,159610607⟩]
theorem checked76001 : checkPrefixCuts (2^48) 9965535233 10 Manual.Count131072.C076001.packed 64 cuts76001 = true := by
 decide +kernel
def cuts76002 : List PrefixCut := [⟨56,139978754,139978842⟩,
⟨64,159523681,159523782⟩]
theorem checked76002 : checkPrefixCuts (2^48) 9965666305 10 Manual.Count131072.C076002.packed 64 cuts76002 = true := by
 decide +kernel
def pointBounds76002 : List (Nat × Nat × Nat) := [(9965780992,116821108219230,116821498324235)]
theorem point_links_checked76002 : (cuts76002.take 1).map (fun c => (9965666305-1+2*2^10*c.k,116820968240476+c.lower,116821358345393+c.upper)) = pointBounds76002 := by
 decide +kernel
def cuts76003 : List PrefixCut := [⟨64,159239135,159239227⟩]
theorem checked76003 : checkPrefixCuts (2^48) 9965797377 10 Manual.Count131072.C076003.packed 64 cuts76003 = true := by
 decide +kernel
def cuts76004 : List PrefixCut := [⟨64,161072875,161072971⟩]
theorem checked76004 : checkPrefixCuts (2^48) 9965928449 10 Manual.Count131072.C076004.packed 64 cuts76004 = true := by
 decide +kernel
def cuts76005 : List PrefixCut := [⟨17,42788599,42788625⟩,
⟨64,158557123,158557219⟩]
theorem checked76005 : checkPrefixCuts (2^48) 9966059521 10 Manual.Count131072.C076005.packed 64 cuts76005 = true := by
 decide +kernel
def pointBounds76005 : List (Nat × Nat × Nat) := [(9966094336,116821490864766,116821880969998)]
theorem point_links_checked76005 : (cuts76005.take 1).map (fun c => (9966059521-1+2*2^10*c.k,116821448076167+c.lower,116821838181373+c.upper)) = pointBounds76005 := by
 decide +kernel
def cuts76006 : List PrefixCut := [⟨64,159854190,159854297⟩]
theorem checked76006 : checkPrefixCuts (2^48) 9966190593 10 Manual.Count131072.C076006.packed 64 cuts76006 = true := by
 decide +kernel
def cuts76007 : List PrefixCut := [⟨42,105344465,105344526⟩,
⟨64,161320701,161320796⟩]
theorem checked76007 : checkPrefixCuts (2^48) 9966321665 10 Manual.Count131072.C076007.packed 64 cuts76007 = true := by
 decide +kernel
def pointBounds76007 : List (Nat × Nat × Nat) := [(9966407680,116821871831945,116822261937415)]
theorem point_links_checked76007 : (cuts76007.take 1).map (fun c => (9966321665-1+2*2^10*c.k,116821766487480+c.lower,116822156592889+c.upper)) = pointBounds76007 := by
 decide +kernel
def cuts76008 : List PrefixCut := [⟨64,161233863,161233953⟩]
theorem checked76008 : checkPrefixCuts (2^48) 9966452737 10 Manual.Count131072.C076008.packed 64 cuts76008 = true := by
 decide +kernel
def cuts76009 : List PrefixCut := [⟨64,162417880,162417978⟩]
theorem checked76009 : checkPrefixCuts (2^48) 9966583809 10 Manual.Count131072.C076009.packed 64 cuts76009 = true := by
 decide +kernel
def cuts76010 : List PrefixCut := [⟨3,7342786,7342789⟩,
⟨64,160636547,160636644⟩]
theorem checked76010 : checkPrefixCuts (2^48) 9966714881 10 Manual.Count131072.C076010.packed 64 cuts76010 = true := by
 decide +kernel
def pointBounds76010 : List (Nat × Nat × Nat) := [(9966721024,116822258802710,116822648908405)]
theorem point_links_checked76010 : (cuts76010.take 1).map (fun c => (9966714881-1+2*2^10*c.k,116822251459924+c.lower,116822641565616+c.upper)) = pointBounds76010 := by
 decide +kernel
def cuts76011 : List PrefixCut := [⟨64,160493227,160493322⟩]
theorem checked76011 : checkPrefixCuts (2^48) 9966845953 10 Manual.Count131072.C076011.packed 64 cuts76011 = true := by
 decide +kernel
def cuts76012 : List PrefixCut := [⟨28,70121576,70121620⟩,
⟨64,160011033,160011133⟩]
theorem checked76012 : checkPrefixCuts (2^48) 9966977025 10 Manual.Count131072.C076012.packed 64 cuts76012 = true := by
 decide +kernel
def pointBounds76012 : List (Nat × Nat × Nat) := [(9967034368,116822642711274,116823032817202)]
theorem point_links_checked76012 : (cuts76012.take 1).map (fun c => (9966977025-1+2*2^10*c.k,116822572589698+c.lower,116822962695582+c.upper)) = pointBounds76012 := by
 decide +kernel
def cuts76013 : List PrefixCut := [⟨64,163538944,163539046⟩]
theorem checked76013 : checkPrefixCuts (2^48) 9967108097 10 Manual.Count131072.C076013.packed 64 cuts76013 = true := by
 decide +kernel
def cuts76014 : List PrefixCut := [⟨53,131287072,131287149⟩,
⟨64,159046666,159046757⟩]
theorem checked76014 : checkPrefixCuts (2^48) 9967239169 10 Manual.Count131072.C076014.packed 64 cuts76014 = true := by
 decide +kernel
def pointBounds76014 : List (Nat × Nat × Nat) := [(9967347712,116823027426747,116823417532910)]
theorem point_links_checked76014 : (cuts76014.take 1).map (fun c => (9967239169-1+2*2^10*c.k,116822896139675+c.lower,116823286245761+c.upper)) = pointBounds76014 := by
 decide +kernel
def cuts76015 : List PrefixCut := [⟨64,161134296,161134394⟩]
theorem checked76015 : checkPrefixCuts (2^48) 9967370241 10 Manual.Count131072.C076015.packed 64 cuts76015 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000187
