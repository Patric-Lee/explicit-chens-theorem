import PlattAssemblyKernel
import PlattCertificates.Count131072.C060000
import PlattCertificates.Count131072.C060001
import PlattCertificates.Count131072.C060002
import PlattCertificates.Count131072.C060003
import PlattCertificates.Count131072.C060004
import PlattCertificates.Count131072.C060005
import PlattCertificates.Count131072.C060006
import PlattCertificates.Count131072.C060007
import PlattCertificates.Count131072.C060008
import PlattCertificates.Count131072.C060009
import PlattCertificates.Count131072.C060010
import PlattCertificates.Count131072.C060011
import PlattCertificates.Count131072.C060012
import PlattCertificates.Count131072.C060013
import PlattCertificates.Count131072.C060014
import PlattCertificates.Count131072.C060015
import PlattCertificates.Count131072.C060016
import PlattCertificates.Count131072.C060017
import PlattCertificates.Count131072.C060018
import PlattCertificates.Count131072.C060019
import PlattCertificates.Count131072.C060020
import PlattCertificates.Count131072.C060021
import PlattCertificates.Count131072.C060022
import PlattCertificates.Count131072.C060023
import PlattCertificates.Count131072.C060024
import PlattCertificates.Count131072.C060025
import PlattCertificates.Count131072.C060026
import PlattCertificates.Count131072.C060027
import PlattCertificates.Count131072.C060028
import PlattCertificates.Count131072.C060029
import PlattCertificates.Count131072.C060030
import PlattCertificates.Count131072.C060031
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60000 : List PrefixCut := [⟨55,174752272,174752374⟩,
⟨64,204229178,204229295⟩]
theorem checked60000 : checkPrefixCuts (2^48) 7868252161 10 Manual.Count131072.C060000.packed 64 cuts60000 = true := by
 decide +kernel
def pointBounds60000 : List (Nat × Nat × Nat) := [(7868364800,113916979950822,113917368358118)]
theorem point_links_checked60000 : (cuts60000.take 1).map (fun c => (7868252161-1+2*2^10*c.k,113916805198550+c.lower,113917193605744+c.upper)) = pointBounds60000 := by
 decide +kernel
def cuts60001 : List PrefixCut := [⟨64,206085970,206086083⟩]
theorem checked60001 : checkPrefixCuts (2^48) 7868383233 10 Manual.Count131072.C060001.packed 64 cuts60001 = true := by
 decide +kernel
def cuts60002 : List PrefixCut := [⟨48,155858958,155859047⟩,
⟨64,205975226,205975345⟩]
theorem checked60002 : checkPrefixCuts (2^48) 7868514305 10 Manual.Count131072.C060002.packed 64 cuts60002 = true := by
 decide +kernel
def pointBounds60002 : List (Nat × Nat × Nat) := [(7868612608,113917371372656,113917759780169)]
theorem point_links_checked60002 : (cuts60002.take 1).map (fun c => (7868514305-1+2*2^10*c.k,113917215513698+c.lower,113917603921122+c.upper)) = pointBounds60002 := by
 decide +kernel
def cuts60003 : List PrefixCut := [⟨64,207831901,207832019⟩]
theorem checked60003 : checkPrefixCuts (2^48) 7868645377 10 Manual.Count131072.C060003.packed 64 cuts60003 = true := by
 decide +kernel
def cuts60004 : List PrefixCut := [⟨41,133139368,133139448⟩,
⟨64,204931015,204931133⟩]
theorem checked60004 : checkPrefixCuts (2^48) 7868776449 10 Manual.Count131072.C060004.packed 64 cuts60004 = true := by
 decide +kernel
def pointBounds60004 : List (Nat × Nat × Nat) := [(7868860416,113917762460193,113918150867934)]
theorem point_links_checked60004 : (cuts60004.take 1).map (fun c => (7868776449-1+2*2^10*c.k,113917629320825+c.lower,113918017728486+c.upper)) = pointBounds60004 := by
 decide +kernel
def cuts60005 : List PrefixCut := [⟨64,202137531,202137646⟩]
theorem checked60005 : checkPrefixCuts (2^48) 7868907521 10 Manual.Count131072.C060005.packed 64 cuts60005 = true := by
 decide +kernel
def cuts60006 : List PrefixCut := [⟨34,110635880,110635944⟩,
⟨64,208214984,208215103⟩]
theorem checked60006 : checkPrefixCuts (2^48) 7869038593 10 Manual.Count131072.C060006.packed 64 cuts60006 = true := by
 decide +kernel
def pointBounds60006 : List (Nat × Nat × Nat) := [(7869108224,113918147025251,113918535433209)]
theorem point_links_checked60006 : (cuts60006.take 1).map (fun c => (7869038593-1+2*2^10*c.k,113918036389371+c.lower,113918424797265+c.upper)) = pointBounds60006 := by
 decide +kernel
def cuts60007 : List PrefixCut := [⟨64,206136922,206137037⟩]
theorem checked60007 : checkPrefixCuts (2^48) 7869169665 10 Manual.Count131072.C060007.packed 64 cuts60007 = true := by
 decide +kernel
def cuts60008 : List PrefixCut := [⟨27,86881945,86881994⟩,
⟨64,204988891,204989012⟩]
theorem checked60008 : checkPrefixCuts (2^48) 7869300737 10 Manual.Count131072.C060008.packed 64 cuts60008 = true := by
 decide +kernel
def pointBounds60008 : List (Nat × Nat × Nat) := [(7869356032,113918537623222,113918926031399)]
theorem point_links_checked60008 : (cuts60008.take 1).map (fun c => (7869300737-1+2*2^10*c.k,113918450741277+c.lower,113918839149405+c.upper)) = pointBounds60008 := by
 decide +kernel
def cuts60009 : List PrefixCut := [⟨64,205271613,205271727⟩]
theorem checked60009 : checkPrefixCuts (2^48) 7869431809 10 Manual.Count131072.C060009.packed 64 cuts60009 = true := by
 decide +kernel
def cuts60010 : List PrefixCut := [⟨20,64810612,64810651⟩,
⟨64,205196669,205196790⟩]
theorem checked60010 : checkPrefixCuts (2^48) 7869562881 10 Manual.Count131072.C060010.packed 64 cuts60010 = true := by
 decide +kernel
def pointBounds60010 : List (Nat × Nat × Nat) := [(7869603840,113918925812393,113919314220795)]
theorem point_links_checked60010 : (cuts60010.take 1).map (fun c => (7869562881-1+2*2^10*c.k,113918861001781+c.lower,113919249410144+c.upper)) = pointBounds60010 := by
 decide +kernel
def cuts60011 : List PrefixCut := [⟨64,203011482,203011601⟩]
theorem checked60011 : checkPrefixCuts (2^48) 7869693953 10 Manual.Count131072.C060011.packed 64 cuts60011 = true := by
 decide +kernel
def cuts60012 : List PrefixCut := [⟨13,41775023,41775044⟩,
⟨64,205297121,205297237⟩]
theorem checked60012 : checkPrefixCuts (2^48) 7869825025 10 Manual.Count131072.C060012.packed 64 cuts60012 = true := by
 decide +kernel
def pointBounds60012 : List (Nat × Nat × Nat) := [(7869851648,113919310984955,113919699393579)]
theorem point_links_checked60012 : (cuts60012.take 1).map (fun c => (7869825025-1+2*2^10*c.k,113919269209932+c.lower,113919657618535+c.upper)) = pointBounds60012 := by
 decide +kernel
def cuts60013 : List PrefixCut := [⟨64,203147765,203147883⟩]
theorem checked60013 : checkPrefixCuts (2^48) 7869956097 10 Manual.Count131072.C060013.packed 64 cuts60013 = true := by
 decide +kernel
def cuts60014 : List PrefixCut := [⟨6,19384701,19384711⟩,
⟨64,203001333,203001450⟩]
theorem checked60014 : checkPrefixCuts (2^48) 7870087169 10 Manual.Count131072.C060014.packed 64 cuts60014 = true := by
 decide +kernel
def pointBounds60014 : List (Nat × Nat × Nat) := [(7870099456,113919697039519,113920085448366)]
theorem point_links_checked60014 : (cuts60014.take 1).map (fun c => (7870087169-1+2*2^10*c.k,113919677654818+c.lower,113920066063655+c.upper)) = pointBounds60014 := by
 decide +kernel
def cuts60015 : List PrefixCut := [⟨63,204535848,204535965⟩,
⟨64,207540021,207540140⟩]
theorem checked60015 : checkPrefixCuts (2^48) 7870218241 10 Manual.Count131072.C060015.packed 64 cuts60015 = true := by
 decide +kernel
def pointBounds60015 : List (Nat × Nat × Nat) := [(7870347264,113920085191999,113920473601070)]
theorem point_links_checked60015 : (cuts60015.take 1).map (fun c => (7870218241-1+2*2^10*c.k,113919880656151+c.lower,113920269065105+c.upper)) = pointBounds60015 := by
 decide +kernel
def cuts60016 : List PrefixCut := [⟨64,206213315,206213436⟩]
theorem checked60016 : checkPrefixCuts (2^48) 7870349313 10 Manual.Count131072.C060016.packed 64 cuts60016 = true := by
 decide +kernel
def cuts60017 : List PrefixCut := [⟨56,178422145,178422250⟩,
⟨64,204493235,204493354⟩]
theorem checked60017 : checkPrefixCuts (2^48) 7870480385 10 Manual.Count131072.C060017.packed 64 cuts60017 = true := by
 decide +kernel
def pointBounds60017 : List (Nat × Nat × Nat) := [(7870595072,113920472831632,113920861240931)]
theorem point_links_checked60017 : (cuts60017.take 1).map (fun c => (7870480385-1+2*2^10*c.k,113920294409487+c.lower,113920682818681+c.upper)) = pointBounds60017 := by
 decide +kernel
def cuts60018 : List PrefixCut := [⟨64,208995914,208996028⟩]
theorem checked60018 : checkPrefixCuts (2^48) 7870611457 10 Manual.Count131072.C060018.packed 64 cuts60018 = true := by
 decide +kernel
def cuts60019 : List PrefixCut := [⟨49,158997635,158997725⟩,
⟨64,207848052,207848171⟩]
theorem checked60019 : checkPrefixCuts (2^48) 7870742529 10 Manual.Count131072.C060019.packed 64 cuts60019 = true := by
 decide +kernel
def pointBounds60019 : List (Nat × Nat × Nat) := [(7870842880,113920866896271,113921255305788)]
theorem point_links_checked60019 : (cuts60019.take 1).map (fun c => (7870742529-1+2*2^10*c.k,113920707898636+c.lower,113921096308063+c.upper)) = pointBounds60019 := by
 decide +kernel
def cuts60020 : List PrefixCut := [⟨64,204947919,204948037⟩]
theorem checked60020 : checkPrefixCuts (2^48) 7870873601 10 Manual.Count131072.C060020.packed 64 cuts60020 = true := by
 decide +kernel
def cuts60021 : List PrefixCut := [⟨42,135712192,135712274⟩,
⟨64,205802761,205802883⟩]
theorem checked60021 : checkPrefixCuts (2^48) 7871004673 10 Manual.Count131072.C060021.packed 64 cuts60021 = true := by
 decide +kernel
def pointBounds60021 : List (Nat × Nat × Nat) := [(7871090688,113921256406799,113921644816545)]
theorem point_links_checked60021 : (cuts60021.take 1).map (fun c => (7871004673-1+2*2^10*c.k,113921120694607+c.lower,113921509104271+c.upper)) = pointBounds60021 := by
 decide +kernel
def cuts60022 : List PrefixCut := [⟨64,206192708,206192827⟩]
theorem checked60022 : checkPrefixCuts (2^48) 7871135745 10 Manual.Count131072.C060022.packed 64 cuts60022 = true := by
 decide +kernel
def cuts60023 : List PrefixCut := [⟨35,114037473,114037537⟩,
⟨64,207190540,207190659⟩]
theorem checked60023 : checkPrefixCuts (2^48) 7871266817 10 Manual.Count131072.C060023.packed 64 cuts60023 = true := by
 decide +kernel
def pointBounds60023 : List (Nat × Nat × Nat) := [(7871338496,113921646727549,113922035137518)]
theorem point_links_checked60023 : (cuts60023.take 1).map (fun c => (7871266817-1+2*2^10*c.k,113921532690076+c.lower,113921921099981+c.upper)) = pointBounds60023 := by
 decide +kernel
def cuts60024 : List PrefixCut := [⟨64,202502664,202502781⟩]
theorem checked60024 : checkPrefixCuts (2^48) 7871397889 10 Manual.Count131072.C060024.packed 64 cuts60024 = true := by
 decide +kernel
def cuts60025 : List PrefixCut := [⟨28,91291384,91291437⟩,
⟨64,206182407,206182527⟩]
theorem checked60025 : checkPrefixCuts (2^48) 7871528961 10 Manual.Count131072.C060025.packed 64 cuts60025 = true := by
 decide +kernel
def pointBounds60025 : List (Nat × Nat × Nat) := [(7871586304,113922033674664,113922422084858)]
theorem point_links_checked60025 : (cuts60025.take 1).map (fun c => (7871528961-1+2*2^10*c.k,113921942383280+c.lower,113922330793421+c.upper)) = pointBounds60025 := by
 decide +kernel
def cuts60026 : List PrefixCut := [⟨64,205606860,205606976⟩]
theorem checked60026 : checkPrefixCuts (2^48) 7871660033 10 Manual.Count131072.C060026.packed 64 cuts60026 = true := by
 decide +kernel
def cuts60027 : List PrefixCut := [⟨21,67688600,67688639⟩,
⟨64,206747662,206747777⟩]
theorem checked60027 : checkPrefixCuts (2^48) 7871791105 10 Manual.Count131072.C060027.packed 64 cuts60027 = true := by
 decide +kernel
def pointBounds60027 : List (Nat × Nat × Nat) := [(7871834112,113922421861147,113922810271563)]
theorem point_links_checked60027 : (cuts60027.take 1).map (fun c => (7871791105-1+2*2^10*c.k,113922354172547+c.lower,113922742582924+c.upper)) = pointBounds60027 := by
 decide +kernel
def cuts60028 : List PrefixCut := [⟨64,207244797,207244917⟩]
theorem checked60028 : checkPrefixCuts (2^48) 7871922177 10 Manual.Count131072.C060028.packed 64 cuts60028 = true := by
 decide +kernel
def cuts60029 : List PrefixCut := [⟨14,44587928,44587956⟩,
⟨64,202056737,202056857⟩]
theorem checked60029 : checkPrefixCuts (2^48) 7872053249 10 Manual.Count131072.C060029.packed 64 cuts60029 = true := by
 decide +kernel
def pointBounds60029 : List (Nat × Nat × Nat) := [(7872081920,113922812752934,113923201163574)]
theorem point_links_checked60029 : (cuts60029.take 1).map (fun c => (7872053249-1+2*2^10*c.k,113922768165006+c.lower,113923156575618+c.upper)) = pointBounds60029 := by
 decide +kernel
def cuts60030 : List PrefixCut := [⟨64,207917252,207917369⟩]
theorem checked60030 : checkPrefixCuts (2^48) 7872184321 10 Manual.Count131072.C060030.packed 64 cuts60030 = true := by
 decide +kernel
def cuts60031 : List PrefixCut := [⟨7,22168099,22168113⟩,
⟨64,204874632,204874748⟩]
theorem checked60031 : checkPrefixCuts (2^48) 7872315393 10 Manual.Count131072.C060031.packed 64 cuts60031 = true := by
 decide +kernel
def pointBounds60031 : List (Nat × Nat × Nat) := [(7872329728,113923200307094,113923588717957)]
theorem point_links_checked60031 : (cuts60031.take 1).map (fun c => (7872315393-1+2*2^10*c.k,113923178138995+c.lower,113923566549844+c.upper)) = pointBounds60031 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000000
