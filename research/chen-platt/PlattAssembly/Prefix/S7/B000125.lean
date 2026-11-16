import PlattAssemblyKernel
import PlattCertificates.Count131072.C064000
import PlattCertificates.Count131072.C064001
import PlattCertificates.Count131072.C064002
import PlattCertificates.Count131072.C064003
import PlattCertificates.Count131072.C064004
import PlattCertificates.Count131072.C064005
import PlattCertificates.Count131072.C064006
import PlattCertificates.Count131072.C064007
import PlattCertificates.Count131072.C064008
import PlattCertificates.Count131072.C064009
import PlattCertificates.Count131072.C064010
import PlattCertificates.Count131072.C064011
import PlattCertificates.Count131072.C064012
import PlattCertificates.Count131072.C064013
import PlattCertificates.Count131072.C064014
import PlattCertificates.Count131072.C064015
import PlattCertificates.Count131072.C064016
import PlattCertificates.Count131072.C064017
import PlattCertificates.Count131072.C064018
import PlattCertificates.Count131072.C064019
import PlattCertificates.Count131072.C064020
import PlattCertificates.Count131072.C064021
import PlattCertificates.Count131072.C064022
import PlattCertificates.Count131072.C064023
import PlattCertificates.Count131072.C064024
import PlattCertificates.Count131072.C064025
import PlattCertificates.Count131072.C064026
import PlattCertificates.Count131072.C064027
import PlattCertificates.Count131072.C064028
import PlattCertificates.Count131072.C064029
import PlattCertificates.Count131072.C064030
import PlattCertificates.Count131072.C064031
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000125
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64000 : List PrefixCut := [⟨63,188586658,188586774⟩,
⟨64,191504480,191504597⟩]
theorem checked64000 : checkPrefixCuts (2^48) 8392540161 10 Manual.Count131072.C064000.packed 64 cuts64000 = true := by
 decide +kernel
def pointBounds64000 : List (Nat × Nat × Nat) := [(8392669184,114712777557261,114713166421240)]
theorem point_links_checked64000 : (cuts64000.take 1).map (fun c => (8392540161-1+2*2^10*c.k,114712588970603+c.lower,114712977834466+c.upper)) = pointBounds64000 := by
 decide +kernel
def cuts64001 : List PrefixCut := [⟨64,192675312,192675423⟩]
theorem checked64001 : checkPrefixCuts (2^48) 8392671233 10 Manual.Count131072.C064001.packed 64 cuts64001 = true := by
 decide +kernel
def cuts64002 : List PrefixCut := [⟨64,191096058,191096167⟩]
theorem checked64002 : checkPrefixCuts (2^48) 8392802305 10 Manual.Count131072.C064002.packed 64 cuts64002 = true := by
 decide +kernel
def pointBounds64002 : List (Nat × Nat × Nat) := [(8392933376,114713164246453,114713553110653)]
theorem point_links_checked64002 : (cuts64002.take 1).map (fun c => (8392802305-1+2*2^10*c.k,114712973150395+c.lower,114713362014486+c.upper)) = pointBounds64002 := by
 decide +kernel
def cuts64003 : List PrefixCut := [⟨64,194379690,194379803⟩]
theorem checked64003 : checkPrefixCuts (2^48) 8392933377 10 Manual.Count131072.C064003.packed 64 cuts64003 = true := by
 decide +kernel
def cuts64004 : List PrefixCut := [⟨64,191559586,191559697⟩]
theorem checked64004 : checkPrefixCuts (2^48) 8393064449 10 Manual.Count131072.C064004.packed 64 cuts64004 = true := by
 decide +kernel
def cuts64005 : List PrefixCut := [⟨1,3253000,3253001⟩,
⟨64,191388947,191389058⟩]
theorem checked64005 : checkPrefixCuts (2^48) 8393195521 10 Manual.Count131072.C064005.packed 64 cuts64005 = true := by
 decide +kernel
def pointBounds64005 : List (Nat × Nat × Nat) := [(8393197568,114713553438729,114713942303154)]
theorem point_links_checked64005 : (cuts64005.take 1).map (fun c => (8393195521-1+2*2^10*c.k,114713550185729+c.lower,114713939050153+c.upper)) = pointBounds64005 := by
 decide +kernel
def cuts64006 : List PrefixCut := [⟨64,191520086,191520201⟩]
theorem checked64006 : checkPrefixCuts (2^48) 8393326593 10 Manual.Count131072.C064006.packed 64 cuts64006 = true := by
 decide +kernel
def cuts64007 : List PrefixCut := [⟨2,6036305,6036308⟩,
⟨64,190443983,190444091⟩]
theorem checked64007 : checkPrefixCuts (2^48) 8393457665 10 Manual.Count131072.C064007.packed 64 cuts64007 = true := by
 decide +kernel
def pointBounds64007 : List (Nat × Nat × Nat) := [(8393461760,114713939131067,114714327995720)]
theorem point_links_checked64007 : (cuts64007.take 1).map (fun c => (8393457665-1+2*2^10*c.k,114713933094762+c.lower,114714321959412+c.upper)) = pointBounds64007 := by
 decide +kernel
def cuts64008 : List PrefixCut := [⟨64,192855467,192855583⟩]
theorem checked64008 : checkPrefixCuts (2^48) 8393588737 10 Manual.Count131072.C064008.packed 64 cuts64008 = true := by
 decide +kernel
def cuts64009 : List PrefixCut := [⟨3,8819436,8819440⟩,
⟨64,190169753,190169861⟩]
theorem checked64009 : checkPrefixCuts (2^48) 8393719809 10 Manual.Count131072.C064009.packed 64 cuts64009 = true := by
 decide +kernel
def pointBounds64009 : List (Nat × Nat × Nat) := [(8393725952,114714325213648,114714714078526)]
theorem point_links_checked64009 : (cuts64009.take 1).map (fun c => (8393719809-1+2*2^10*c.k,114714316394212+c.lower,114714705259086+c.upper)) = pointBounds64009 := by
 decide +kernel
def cuts64010 : List PrefixCut := [⟨64,192648254,192648369⟩]
theorem checked64010 : checkPrefixCuts (2^48) 8393850881 10 Manual.Count131072.C064010.packed 64 cuts64010 = true := by
 decide +kernel
def cuts64011 : List PrefixCut := [⟨4,11770057,11770062⟩,
⟨64,191605728,191605834⟩]
theorem checked64011 : checkPrefixCuts (2^48) 8393981953 10 Manual.Count131072.C064011.packed 64 cuts64011 = true := by
 decide +kernel
def pointBounds64011 : List (Nat × Nat × Nat) := [(8393990144,114714710982276,114715099847378)]
theorem point_links_checked64011 : (cuts64011.take 1).map (fun c => (8393981953-1+2*2^10*c.k,114714699212219+c.lower,114715088077316+c.upper)) = pointBounds64011 := by
 decide +kernel
def cuts64012 : List PrefixCut := [⟨64,189456677,189456789⟩]
theorem checked64012 : checkPrefixCuts (2^48) 8394113025 10 Manual.Count131072.C064012.packed 64 cuts64012 = true := by
 decide +kernel
def cuts64013 : List PrefixCut := [⟨5,14921684,14921692⟩,
⟨64,192136232,192136345⟩]
theorem checked64013 : checkPrefixCuts (2^48) 8394244097 10 Manual.Count131072.C064013.packed 64 cuts64013 = true := by
 decide +kernel
def pointBounds64013 : List (Nat × Nat × Nat) := [(8394254336,114715095196308,114715484061631)]
theorem point_links_checked64013 : (cuts64013.take 1).map (fun c => (8394244097-1+2*2^10*c.k,114715080274624+c.lower,114715469139939+c.upper)) = pointBounds64013 := by
 decide +kernel
def cuts64014 : List PrefixCut := [⟨64,193373892,193374005⟩]
theorem checked64014 : checkPrefixCuts (2^48) 8394375169 10 Manual.Count131072.C064014.packed 64 cuts64014 = true := by
 decide +kernel
def cuts64015 : List PrefixCut := [⟨6,18911384,18911394⟩,
⟨64,192599676,192599788⟩]
theorem checked64015 : checkPrefixCuts (2^48) 8394506241 10 Manual.Count131072.C064015.packed 64 cuts64015 = true := by
 decide +kernel
def pointBounds64015 : List (Nat × Nat × Nat) := [(8394518528,114715484696132,114715873561683)]
theorem point_links_checked64015 : (cuts64015.take 1).map (fun c => (8394506241-1+2*2^10*c.k,114715465784748+c.lower,114715854650289+c.upper)) = pointBounds64015 := by
 decide +kernel
def cuts64016 : List PrefixCut := [⟨64,190484278,190484383⟩]
theorem checked64016 : checkPrefixCuts (2^48) 8394637313 10 Manual.Count131072.C064016.packed 64 cuts64016 = true := by
 decide +kernel
def cuts64017 : List PrefixCut := [⟨7,21190815,21190829⟩,
⟨64,191487185,191487297⟩]
theorem checked64017 : checkPrefixCuts (2^48) 8394768385 10 Manual.Count131072.C064017.packed 64 cuts64017 = true := by
 decide +kernel
def pointBounds64017 : List (Nat × Nat × Nat) := [(8394782720,114715870059517,114716258925289)]
theorem point_links_checked64017 : (cuts64017.take 1).map (fun c => (8394768385-1+2*2^10*c.k,114715848868702+c.lower,114716237734460+c.upper)) = pointBounds64017 := by
 decide +kernel
def cuts64018 : List PrefixCut := [⟨64,191752423,191752536⟩]
theorem checked64018 : checkPrefixCuts (2^48) 8394899457 10 Manual.Count131072.C064018.packed 64 cuts64018 = true := by
 decide +kernel
def cuts64019 : List PrefixCut := [⟨8,24543021,24543035⟩,
⟨64,193526452,193526566⟩]
theorem checked64019 : checkPrefixCuts (2^48) 8395030529 10 Manual.Count131072.C064019.packed 64 cuts64019 = true := by
 decide +kernel
def pointBounds64019 : List (Nat × Nat × Nat) := [(8395046912,114716256651331,114716645517328)]
theorem point_links_checked64019 : (cuts64019.take 1).map (fun c => (8395030529-1+2*2^10*c.k,114716232108310+c.lower,114716620974293+c.upper)) = pointBounds64019 := by
 decide +kernel
def cuts64020 : List PrefixCut := [⟨64,193020520,193020629⟩]
theorem checked64020 : checkPrefixCuts (2^48) 8395161601 10 Manual.Count131072.C064020.packed 64 cuts64020 = true := by
 decide +kernel
def cuts64021 : List PrefixCut := [⟨9,28263825,28263841⟩,
⟨64,195565595,195565704⟩]
theorem checked64021 : checkPrefixCuts (2^48) 8395292673 10 Manual.Count131072.C064021.packed 64 cuts64021 = true := by
 decide +kernel
def pointBounds64021 : List (Nat × Nat × Nat) := [(8395311104,114716646919107,114717035785329)]
theorem point_links_checked64021 : (cuts64021.take 1).map (fun c => (8395292673-1+2*2^10*c.k,114716618655282+c.lower,114717007521488+c.upper)) = pointBounds64021 := by
 decide +kernel
def cuts64022 : List PrefixCut := [⟨64,190198206,190198310⟩]
theorem checked64022 : checkPrefixCuts (2^48) 8395423745 10 Manual.Count131072.C064022.packed 64 cuts64022 = true := by
 decide +kernel
def cuts64023 : List PrefixCut := [⟨10,29671057,29671074⟩,
⟨64,192072730,192072839⟩]
theorem checked64023 : checkPrefixCuts (2^48) 8395554817 10 Manual.Count131072.C064023.packed 64 cuts64023 = true := by
 decide +kernel
def pointBounds64023 : List (Nat × Nat × Nat) := [(8395575296,114717034090140,114717422956576)]
theorem point_links_checked64023 : (cuts64023.take 1).map (fun c => (8395554817-1+2*2^10*c.k,114717004419083+c.lower,114717393285502+c.upper)) = pointBounds64023 := by
 decide +kernel
def cuts64024 : List PrefixCut := [⟨64,193712491,193712598⟩]
theorem checked64024 : checkPrefixCuts (2^48) 8395685889 10 Manual.Count131072.C064024.packed 64 cuts64024 = true := by
 decide +kernel
def cuts64025 : List PrefixCut := [⟨11,33022682,33022701⟩,
⟨64,189585856,189585966⟩]
theorem checked64025 : checkPrefixCuts (2^48) 8395816961 10 Manual.Count131072.C064025.packed 64 cuts64025 = true := by
 decide +kernel
def pointBounds64025 : List (Nat × Nat × Nat) := [(8395839488,114717423226986,114717812093640)]
theorem point_links_checked64025 : (cuts64025.take 1).map (fun c => (8395816961-1+2*2^10*c.k,114717390204304+c.lower,114717779070939+c.upper)) = pointBounds64025 := by
 decide +kernel
def cuts64026 : List PrefixCut := [⟨64,196656636,196656750⟩]
theorem checked64026 : checkPrefixCuts (2^48) 8395948033 10 Manual.Count131072.C064026.packed 64 cuts64026 = true := by
 decide +kernel
def cuts64027 : List PrefixCut := [⟨12,37849179,37849199⟩,
⟨64,196150714,196150823⟩]
theorem checked64027 : checkPrefixCuts (2^48) 8396079105 10 Manual.Count131072.C064027.packed 64 cuts64027 = true := by
 decide +kernel
def pointBounds64027 : List (Nat × Nat × Nat) := [(8396103680,114717814295975,114718203162854)]
theorem point_links_checked64027 : (cuts64027.take 1).map (fun c => (8396079105-1+2*2^10*c.k,114717776446796+c.lower,114718165313655+c.upper)) = pointBounds64027 := by
 decide +kernel
def cuts64028 : List PrefixCut := [⟨64,192191830,192191938⟩]
theorem checked64028 : checkPrefixCuts (2^48) 8396210177 10 Manual.Count131072.C064028.packed 64 cuts64028 = true := by
 decide +kernel
def cuts64029 : List PrefixCut := [⟨13,38484936,38484958⟩,
⟨64,190479138,190479246⟩]
theorem checked64029 : checkPrefixCuts (2^48) 8396341249 10 Manual.Count131072.C064029.packed 64 cuts64029 = true := by
 decide +kernel
def pointBounds64029 : List (Nat × Nat × Nat) := [(8396367872,114718203274276,114718592141374)]
theorem point_links_checked64029 : (cuts64029.take 1).map (fun c => (8396341249-1+2*2^10*c.k,114718164789340+c.lower,114718553656416+c.upper)) = pointBounds64029 := by
 decide +kernel
def cuts64030 : List PrefixCut := [⟨64,191481855,191481967⟩]
theorem checked64030 : checkPrefixCuts (2^48) 8396472321 10 Manual.Count131072.C064030.packed 64 cuts64030 = true := by
 decide +kernel
def cuts64031 : List PrefixCut := [⟨14,40193372,40193397⟩,
⟨64,188964683,188964798⟩]
theorem checked64031 : checkPrefixCuts (2^48) 8396603393 10 Manual.Count131072.C064031.packed 64 cuts64031 = true := by
 decide +kernel
def pointBounds64031 : List (Nat × Nat × Nat) := [(8396632064,114718586943705,114718975811026)]
theorem point_links_checked64031 : (cuts64031.take 1).map (fun c => (8396603393-1+2*2^10*c.k,114718546750333+c.lower,114718935617629+c.upper)) = pointBounds64031 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000125
