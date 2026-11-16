import PlattAssemblyKernel
import PlattCertificates.Count131072.C046016
import PlattCertificates.Count131072.C046017
import PlattCertificates.Count131072.C046018
import PlattCertificates.Count131072.C046019
import PlattCertificates.Count131072.C046020
import PlattCertificates.Count131072.C046021
import PlattCertificates.Count131072.C046022
import PlattCertificates.Count131072.C046023
import PlattCertificates.Count131072.C046024
import PlattCertificates.Count131072.C046025
import PlattCertificates.Count131072.C046026
import PlattCertificates.Count131072.C046027
import PlattCertificates.Count131072.C046028
import PlattCertificates.Count131072.C046029
import PlattCertificates.Count131072.C046030
import PlattCertificates.Count131072.C046031
import PlattCertificates.Count131072.C046032
import PlattCertificates.Count131072.C046033
import PlattCertificates.Count131072.C046034
import PlattCertificates.Count131072.C046035
import PlattCertificates.Count131072.C046036
import PlattCertificates.Count131072.C046037
import PlattCertificates.Count131072.C046038
import PlattCertificates.Count131072.C046039
import PlattCertificates.Count131072.C046040
import PlattCertificates.Count131072.C046041
import PlattCertificates.Count131072.C046042
import PlattCertificates.Count131072.C046043
import PlattCertificates.Count131072.C046044
import PlattCertificates.Count131072.C046045
import PlattCertificates.Count131072.C046046
import PlattCertificates.Count131072.C046047
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000188
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts46016 : List PrefixCut := [⟨64,272454950,272455112⟩]
theorem checked46016 : checkPrefixCuts (2^48) 6035341313 10 Manual.Count131072.C046016.packed 64 cuts46016 = true := by
 decide +kernel
def cuts46017 : List PrefixCut := [⟨18,77136973,77137019⟩,
⟨64,271283118,271283273⟩]
theorem checked46017 : checkPrefixCuts (2^48) 6035472385 10 Manual.Count131072.C046017.packed 64 cuts46017 = true := by
 decide +kernel
def pointBounds46017 : List (Nat × Nat × Nat) := [(6035509248,110621955513405,110622342043593)]
theorem point_links_checked46017 : (cuts46017.take 1).map (fun c => (6035472385-1+2*2^10*c.k,110621878376432+c.lower,110622264906574+c.upper)) = pointBounds46017 := by
 decide +kernel
def cuts46018 : List PrefixCut := [⟨47,200112414,200112529⟩,
⟨64,271090686,271090841⟩]
theorem checked46018 : checkPrefixCuts (2^48) 6035603457 10 Manual.Count131072.C046018.packed 64 cuts46018 = true := by
 decide +kernel
def pointBounds46018 : List (Nat × Nat × Nat) := [(6035699712,110622349771964,110622736302376)]
theorem point_links_checked46018 : (cuts46018.take 1).map (fun c => (6035603457-1+2*2^10*c.k,110622149659550+c.lower,110622536189847+c.upper)) = pointBounds46018 := by
 decide +kernel
def cuts46019 : List PrefixCut := [⟨64,273976115,273976271⟩]
theorem checked46019 : checkPrefixCuts (2^48) 6035734529 10 Manual.Count131072.C046019.packed 64 cuts46019 = true := by
 decide +kernel
def cuts46020 : List PrefixCut := [⟨12,49711451,49711479⟩,
⟨64,268374171,268374326⟩]
theorem checked46020 : checkPrefixCuts (2^48) 6035865601 10 Manual.Count131072.C046020.packed 64 cuts46020 = true := by
 decide +kernel
def pointBounds46020 : List (Nat × Nat × Nat) := [(6035890176,110622744437802,110623130968438)]
theorem point_links_checked46020 : (cuts46020.take 1).map (fun c => (6035865601-1+2*2^10*c.k,110622694726351+c.lower,110623081256959+c.upper)) = pointBounds46020 := by
 decide +kernel
def cuts46021 : List PrefixCut := [⟨41,172773004,172773104⟩,
⟨64,270933113,270933266⟩]
theorem checked46021 : checkPrefixCuts (2^48) 6035996673 10 Manual.Count131072.C046021.packed 64 cuts46021 = true := by
 decide +kernel
def pointBounds46021 : List (Nat × Nat × Nat) := [(6036080640,110623135873526,110623522404389)]
theorem point_links_checked46021 : (cuts46021.take 1).map (fun c => (6035996673-1+2*2^10*c.k,110622963100522+c.lower,110623349631285+c.upper)) = pointBounds46021 := by
 decide +kernel
def cuts46022 : List PrefixCut := [⟨64,269108622,269108777⟩]
theorem checked46022 : checkPrefixCuts (2^48) 6036127745 10 Manual.Count131072.C046022.packed 64 cuts46022 = true := by
 decide +kernel
def cuts46023 : List PrefixCut := [⟨6,26392943,26392957⟩,
⟨64,275397861,275398019⟩]
theorem checked46023 : checkPrefixCuts (2^48) 6036258817 10 Manual.Count131072.C046023.packed 64 cuts46023 = true := by
 decide +kernel
def pointBounds46023 : List (Nat × Nat × Nat) := [(6036271104,110623529535200,110623916066285)]
theorem point_links_checked46023 : (cuts46023.take 1).map (fun c => (6036258817-1+2*2^10*c.k,110623503142257+c.lower,110623889673328+c.upper)) = pointBounds46023 := by
 decide +kernel
def cuts46024 : List PrefixCut := [⟨35,150473072,150473158⟩,
⟨64,270822240,270822394⟩]
theorem checked46024 : checkPrefixCuts (2^48) 6036389889 10 Manual.Count131072.C046024.packed 64 cuts46024 = true := by
 decide +kernel
def pointBounds46024 : List (Nat × Nat × Nat) := [(6036461568,110623929013190,110624315544505)]
theorem point_links_checked46024 : (cuts46024.take 1).map (fun c => (6036389889-1+2*2^10*c.k,110623778540118+c.lower,110624165071347+c.upper)) = pointBounds46024 := by
 decide +kernel
def cuts46025 : List PrefixCut := [⟨64,269883748,269883907⟩]
theorem checked46025 : checkPrefixCuts (2^48) 6036520961 10 Manual.Count131072.C046025.packed 64 cuts46025 = true := by
 decide +kernel
def pointBounds46025 : List (Nat × Nat × Nat) := [(6036652032,110624319246106,110624705777648)]
theorem point_links_checked46025 : (cuts46025.take 1).map (fun c => (6036520961-1+2*2^10*c.k,110624049362358+c.lower,110624435893741+c.upper)) = pointBounds46025 := by
 decide +kernel
def cuts46026 : List PrefixCut := [⟨64,272489031,272489188⟩]
theorem checked46026 : checkPrefixCuts (2^48) 6036652033 10 Manual.Count131072.C046026.packed 64 cuts46026 = true := by
 decide +kernel
def cuts46027 : List PrefixCut := [⟨29,124212749,124212820⟩,
⟨64,272716266,272716423⟩]
theorem checked46027 : checkPrefixCuts (2^48) 6036783105 10 Manual.Count131072.C046027.packed 64 cuts46027 = true := by
 decide +kernel
def pointBounds46027 : List (Nat × Nat × Nat) := [(6036842496,110624715947886,110625102479656)]
theorem point_links_checked46027 : (cuts46027.take 1).map (fun c => (6036783105-1+2*2^10*c.k,110624591735137+c.lower,110624978266836+c.upper)) = pointBounds46027 := by
 decide +kernel
def cuts46028 : List PrefixCut := [⟨58,245061885,245062025⟩,
⟨64,271311569,271311723⟩]
theorem checked46028 : checkPrefixCuts (2^48) 6036914177 10 Manual.Count131072.C046028.packed 64 cuts46028 = true := by
 decide +kernel
def pointBounds46028 : List (Nat × Nat × Nat) := [(6037032960,110625109513288,110625496045284)]
theorem point_links_checked46028 : (cuts46028.take 1).map (fun c => (6036914177-1+2*2^10*c.k,110624864451403+c.lower,110625250983259+c.upper)) = pointBounds46028 := by
 decide +kernel
def cuts46029 : List PrefixCut := [⟨64,275315332,275315493⟩]
theorem checked46029 : checkPrefixCuts (2^48) 6037045249 10 Manual.Count131072.C046029.packed 64 cuts46029 = true := by
 decide +kernel
def cuts46030 : List PrefixCut := [⟨23,97582820,97582877⟩,
⟨64,272278870,272279030⟩]
theorem checked46030 : checkPrefixCuts (2^48) 6037176321 10 Manual.Count131072.C046030.packed 64 cuts46030 = true := by
 decide +kernel
def pointBounds46030 : List (Nat × Nat × Nat) := [(6037223424,110625508661124,110625895193352)]
theorem point_links_checked46030 : (cuts46030.take 1).map (fun c => (6037176321-1+2*2^10*c.k,110625411078304+c.lower,110625797610475+c.upper)) = pointBounds46030 := by
 decide +kernel
def cuts46031 : List PrefixCut := [⟨52,220522891,220523020⟩,
⟨64,271899971,271900131⟩]
theorem checked46031 : checkPrefixCuts (2^48) 6037307393 10 Manual.Count131072.C046031.packed 64 cuts46031 = true := by
 decide +kernel
def pointBounds46031 : List (Nat × Nat × Nat) := [(6037413888,110625903880065,110626290412525)]
theorem point_links_checked46031 : (cuts46031.take 1).map (fun c => (6037307393-1+2*2^10*c.k,110625683357174+c.lower,110626069889505+c.upper)) = pointBounds46031 := by
 decide +kernel
def cuts46032 : List PrefixCut := [⟨64,269376516,269376672⟩]
theorem checked46032 : checkPrefixCuts (2^48) 6037438465 10 Manual.Count131072.C046032.packed 64 cuts46032 = true := by
 decide +kernel
def cuts46033 : List PrefixCut := [⟨17,70023884,70023927⟩,
⟨64,270069982,270070139⟩]
theorem checked46033 : checkPrefixCuts (2^48) 6037569537 10 Manual.Count131072.C046033.packed 64 cuts46033 = true := by
 decide +kernel
def pointBounds46033 : List (Nat × Nat × Nat) := [(6037604352,110626294657545,110626681190235)]
theorem point_links_checked46033 : (cuts46033.take 1).map (fun c => (6037569537-1+2*2^10*c.k,110626224633661+c.lower,110626611166308+c.upper)) = pointBounds46033 := by
 decide +kernel
def cuts46034 : List PrefixCut := [⟨46,194868200,194868314⟩,
⟨64,269924273,269924433⟩]
theorem checked46034 : checkPrefixCuts (2^48) 6037700609 10 Manual.Count131072.C046034.packed 64 cuts46034 = true := by
 decide +kernel
def pointBounds46034 : List (Nat × Nat × Nat) := [(6037794816,110626689571843,110627076104761)]
theorem point_links_checked46034 : (cuts46034.take 1).map (fun c => (6037700609-1+2*2^10*c.k,110626494703643+c.lower,110626881236447+c.upper)) = pointBounds46034 := by
 decide +kernel
def cuts46035 : List PrefixCut := [⟨64,271083863,271084020⟩]
theorem checked46035 : checkPrefixCuts (2^48) 6037831681 10 Manual.Count131072.C046035.packed 64 cuts46035 = true := by
 decide +kernel
def cuts46036 : List PrefixCut := [⟨11,46477591,46477617⟩,
⟨64,272802808,272802965⟩]
theorem checked46036 : checkPrefixCuts (2^48) 6037962753 10 Manual.Count131072.C046036.packed 64 cuts46036 = true := by
 decide +kernel
def pointBounds46036 : List (Nat × Nat × Nat) := [(6037985280,110627082189370,110627468722517)]
theorem point_links_checked46036 : (cuts46036.take 1).map (fun c => (6037962753-1+2*2^10*c.k,110627035711779+c.lower,110627422244900+c.upper)) = pointBounds46036 := by
 decide +kernel
def cuts46037 : List PrefixCut := [⟨40,165673972,165674065⟩,
⟨64,267296181,267296333⟩]
theorem checked46037 : checkPrefixCuts (2^48) 6038093825 10 Manual.Count131072.C046037.packed 64 cuts46037 = true := by
 decide +kernel
def pointBounds46037 : List (Nat × Nat × Nat) := [(6038175744,110627474188559,110627860721930)]
theorem point_links_checked46037 : (cuts46037.take 1).map (fun c => (6038093825-1+2*2^10*c.k,110627308514587+c.lower,110627695047865+c.upper)) = pointBounds46037 := by
 decide +kernel
def cuts46038 : List PrefixCut := [⟨64,271252671,271252831⟩]
theorem checked46038 : checkPrefixCuts (2^48) 6038224897 10 Manual.Count131072.C046038.packed 64 cuts46038 = true := by
 decide +kernel
def cuts46039 : List PrefixCut := [⟨5,20090830,20090840⟩,
⟨64,271666292,271666445⟩]
theorem checked46039 : checkPrefixCuts (2^48) 6038355969 10 Manual.Count131072.C046039.packed 64 cuts46039 = true := by
 decide +kernel
def pointBounds46039 : List (Nat × Nat × Nat) := [(6038366208,110627867154269,110628253687869)]
theorem point_links_checked46039 : (cuts46039.take 1).map (fun c => (6038355969-1+2*2^10*c.k,110627847063439+c.lower,110628233597029+c.upper)) = pointBounds46039 := by
 decide +kernel
def cuts46040 : List PrefixCut := [⟨34,143801743,143801827⟩,
⟨64,271147650,271147806⟩]
theorem checked46040 : checkPrefixCuts (2^48) 6038487041 10 Manual.Count131072.C046040.packed 64 cuts46040 = true := by
 decide +kernel
def pointBounds46040 : List (Nat × Nat × Nat) := [(6038556672,110628262531474,110628649065301)]
theorem point_links_checked46040 : (cuts46040.take 1).map (fun c => (6038487041-1+2*2^10*c.k,110628118729731+c.lower,110628505263474+c.upper)) = pointBounds46040 := by
 decide +kernel
def cuts46041 : List PrefixCut := [⟨63,267226461,267226608⟩,
⟨64,271188435,271188585⟩]
theorem checked46041 : checkPrefixCuts (2^48) 6038618113 10 Manual.Count131072.C046041.packed 64 cuts46041 = true := by
 decide +kernel
def pointBounds46041 : List (Nat × Nat × Nat) := [(6038747136,110628657103842,110629043637888)]
theorem point_links_checked46041 : (cuts46041.take 1).map (fun c => (6038618113-1+2*2^10*c.k,110628389877381+c.lower,110628776411280+c.upper)) = pointBounds46041 := by
 decide +kernel
def cuts46042 : List PrefixCut := [⟨64,272441026,272441179⟩]
theorem checked46042 : checkPrefixCuts (2^48) 6038749185 10 Manual.Count131072.C046042.packed 64 cuts46042 = true := by
 decide +kernel
def cuts46043 : List PrefixCut := [⟨28,120021327,120021396⟩,
⟨64,271176635,271176789⟩]
theorem checked46043 : checkPrefixCuts (2^48) 6038880257 10 Manual.Count131072.C046043.packed 64 cuts46043 = true := by
 decide +kernel
def pointBounds46043 : List (Nat × Nat × Nat) := [(6038937600,110629053528169,110629440062440)]
theorem point_links_checked46043 : (cuts46043.take 1).map (fun c => (6038880257-1+2*2^10*c.k,110628933506842+c.lower,110629320041044+c.upper)) = pointBounds46043 := by
 decide +kernel
def cuts46044 : List PrefixCut := [⟨57,239010883,239011023⟩,
⟨64,269865695,269865851⟩]
theorem checked46044 : checkPrefixCuts (2^48) 6039011329 10 Manual.Count131072.C046044.packed 64 cuts46044 = true := by
 decide +kernel
def pointBounds46044 : List (Nat × Nat × Nat) := [(6039128064,110629443694360,110629830228856)]
theorem point_links_checked46044 : (cuts46044.take 1).map (fun c => (6039011329-1+2*2^10*c.k,110629204683477+c.lower,110629591217833+c.upper)) = pointBounds46044 := by
 decide +kernel
def cuts46045 : List PrefixCut := [⟨64,270372513,270372671⟩]
theorem checked46045 : checkPrefixCuts (2^48) 6039142401 10 Manual.Count131072.C046045.packed 64 cuts46045 = true := by
 decide +kernel
def cuts46046 : List PrefixCut := [⟨22,93354290,93354345⟩,
⟨64,273116444,273116600⟩]
theorem checked46046 : checkPrefixCuts (2^48) 6039273473 10 Manual.Count131072.C046046.packed 64 cuts46046 = true := by
 decide +kernel
def pointBounds46046 : List (Nat × Nat × Nat) := [(6039318528,110629838275975,110630224810700)]
theorem point_links_checked46046 : (cuts46046.take 1).map (fun c => (6039273473-1+2*2^10*c.k,110629744921685+c.lower,110630131456355+c.upper)) = pointBounds46046 := by
 decide +kernel
def cuts46047 : List PrefixCut := [⟨51,218209286,218209411⟩,
⟨64,272225051,272225207⟩]
theorem checked46047 : checkPrefixCuts (2^48) 6039404545 10 Manual.Count131072.C046047.packed 64 cuts46047 = true := by
 decide +kernel
def pointBounds46047 : List (Nat × Nat × Nat) := [(6039508992,110630236247415,110630622782366)]
theorem point_links_checked46047 : (cuts46047.take 1).map (fun c => (6039404545-1+2*2^10*c.k,110630018038129+c.lower,110630404572955+c.upper)) = pointBounds46047 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000188
