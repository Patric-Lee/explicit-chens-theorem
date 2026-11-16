import PlattAssemblyKernel
import PlattCertificates.Count131072.C064992
import PlattCertificates.Count131072.C064993
import PlattCertificates.Count131072.C064994
import PlattCertificates.Count131072.C064995
import PlattCertificates.Count131072.C064996
import PlattCertificates.Count131072.C064997
import PlattCertificates.Count131072.C064998
import PlattCertificates.Count131072.C064999
import PlattCertificates.Count131072.C065000
import PlattCertificates.Count131072.C065001
import PlattCertificates.Count131072.C065002
import PlattCertificates.Count131072.C065003
import PlattCertificates.Count131072.C065004
import PlattCertificates.Count131072.C065005
import PlattCertificates.Count131072.C065006
import PlattCertificates.Count131072.C065007
import PlattCertificates.Count131072.C065008
import PlattCertificates.Count131072.C065009
import PlattCertificates.Count131072.C065010
import PlattCertificates.Count131072.C065011
import PlattCertificates.Count131072.C065012
import PlattCertificates.Count131072.C065013
import PlattCertificates.Count131072.C065014
import PlattCertificates.Count131072.C065015
import PlattCertificates.Count131072.C065016
import PlattCertificates.Count131072.C065017
import PlattCertificates.Count131072.C065018
import PlattCertificates.Count131072.C065019
import PlattCertificates.Count131072.C065020
import PlattCertificates.Count131072.C065021
import PlattCertificates.Count131072.C065022
import PlattCertificates.Count131072.C065023
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000156
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64992 : List PrefixCut := [⟨53,156580114,156580205⟩,
⟨64,188781007,188781117⟩]
theorem checked64992 : checkPrefixCuts (2^48) 8522563585 10 Manual.Count131072.C064992.packed 64 cuts64992 = true := by
 decide +kernel
def pointBounds64992 : List (Nat × Nat × Nat) := [(8522672128,114902052516175,114902441489424)]
theorem point_links_checked64992 : (cuts64992.take 1).map (fun c => (8522563585-1+2*2^10*c.k,114901895936061+c.lower,114902284909219+c.upper)) = pointBounds64992 := by
 decide +kernel
def cuts64993 : List PrefixCut := [⟨64,190132186,190132296⟩]
theorem checked64993 : checkPrefixCuts (2^48) 8522694657 10 Manual.Count131072.C064993.packed 64 cuts64993 = true := by
 decide +kernel
def cuts64994 : List PrefixCut := [⟨56,164435376,164435471⟩,
⟨64,187916528,187916638⟩]
theorem checked64994 : checkPrefixCuts (2^48) 8522825729 10 Manual.Count131072.C064994.packed 64 cuts64994 = true := by
 decide +kernel
def pointBounds64994 : List (Nat × Nat × Nat) := [(8522940416,114902439284630,114902828258103)]
theorem point_links_checked64994 : (cuts64994.take 1).map (fun c => (8522825729-1+2*2^10*c.k,114902274849254+c.lower,114902663822632+c.upper)) = pointBounds64994 := by
 decide +kernel
def cuts64995 : List PrefixCut := [⟨64,191084066,191084174⟩]
theorem checked64995 : checkPrefixCuts (2^48) 8522956801 10 Manual.Count131072.C064995.packed 64 cuts64995 = true := by
 decide +kernel
def cuts64996 : List PrefixCut := [⟨59,176814548,176814647⟩,
⟨64,191411378,191411485⟩]
theorem checked64996 : checkPrefixCuts (2^48) 8523087873 10 Manual.Count131072.C064996.packed 64 cuts64996 = true := by
 decide +kernel
def pointBounds64996 : List (Nat × Nat × Nat) := [(8523208704,114902830664396,114903219638091)]
theorem point_links_checked64996 : (cuts64996.take 1).map (fun c => (8523087873-1+2*2^10*c.k,114902653849848+c.lower,114903042823444+c.upper)) = pointBounds64996 := by
 decide +kernel
def cuts64997 : List PrefixCut := [⟨64,190054436,190054547⟩]
theorem checked64997 : checkPrefixCuts (2^48) 8523218945 10 Manual.Count131072.C064997.packed 64 cuts64997 = true := by
 decide +kernel
def cuts64998 : List PrefixCut := [⟨62,183677979,183678084⟩,
⟨64,189589181,189589289⟩]
theorem checked64998 : checkPrefixCuts (2^48) 8523350017 10 Manual.Count131072.C064998.packed 64 cuts64998 = true := by
 decide +kernel
def pointBounds64998 : List (Nat × Nat × Nat) := [(8523476992,114903218993641,114903607967560)]
theorem point_links_checked64998 : (cuts64998.take 1).map (fun c => (8523350017-1+2*2^10*c.k,114903035315662+c.lower,114903424289476+c.upper)) = pointBounds64998 := by
 decide +kernel
def cuts64999 : List PrefixCut := [⟨64,187142549,187142661⟩]
theorem checked64999 : checkPrefixCuts (2^48) 8523481089 10 Manual.Count131072.C064999.packed 64 cuts64999 = true := by
 decide +kernel
def cuts65000 : List PrefixCut := [⟨64,192060043,192060157⟩]
theorem checked65000 : checkPrefixCuts (2^48) 8523612161 10 Manual.Count131072.C065000.packed 64 cuts65000 = true := by
 decide +kernel
def cuts65001 : List PrefixCut := [⟨1,2542728,2542730⟩,
⟨64,190934340,190934450⟩]
theorem checked65001 : checkPrefixCuts (2^48) 8523743233 10 Manual.Count131072.C065001.packed 64 cuts65001 = true := by
 decide +kernel
def pointBounds65001 : List (Nat × Nat × Nat) := [(8523745280,114903606650163,114903995624313)]
theorem point_links_checked65001 : (cuts65001.take 1).map (fun c => (8523743233-1+2*2^10*c.k,114903604107435+c.lower,114903993081583+c.upper)) = pointBounds65001 := by
 decide +kernel
def cuts65002 : List PrefixCut := [⟨64,186902761,186902871⟩]
theorem checked65002 : checkPrefixCuts (2^48) 8523874305 10 Manual.Count131072.C065002.packed 64 cuts65002 = true := by
 decide +kernel
def cuts65003 : List PrefixCut := [⟨4,11722604,11722611⟩,
⟨64,189772723,189772830⟩]
theorem checked65003 : checkPrefixCuts (2^48) 8524005377 10 Manual.Count131072.C065003.packed 64 cuts65003 = true := by
 decide +kernel
def pointBounds65003 : List (Nat × Nat × Nat) := [(8524013568,114903993667140,114904382641515)]
theorem point_links_checked65003 : (cuts65003.take 1).map (fun c => (8524005377-1+2*2^10*c.k,114903981944536+c.lower,114904370918904+c.upper)) = pointBounds65003 := by
 decide +kernel
def cuts65004 : List PrefixCut := [⟨64,188911277,188911391⟩]
theorem checked65004 : checkPrefixCuts (2^48) 8524136449 10 Manual.Count131072.C065004.packed 64 cuts65004 = true := by
 decide +kernel
def cuts65005 : List PrefixCut := [⟨7,20934929,20934941⟩,
⟨64,190196167,190196271⟩]
theorem checked65005 : checkPrefixCuts (2^48) 8524267521 10 Manual.Count131072.C065005.packed 64 cuts65005 = true := by
 decide +kernel
def pointBounds65005 : List (Nat × Nat × Nat) := [(8524281856,114904381563465,114904770538066)]
theorem point_links_checked65005 : (cuts65005.take 1).map (fun c => (8524267521-1+2*2^10*c.k,114904360628536+c.lower,114904749603125+c.upper)) = pointBounds65005 := by
 decide +kernel
def cuts65006 : List PrefixCut := [⟨64,187881857,187881966⟩]
theorem checked65006 : checkPrefixCuts (2^48) 8524398593 10 Manual.Count131072.C065006.packed 64 cuts65006 = true := by
 decide +kernel
def cuts65007 : List PrefixCut := [⟨10,30113661,30113679⟩,
⟨64,193029954,193030068⟩]
theorem checked65007 : checkPrefixCuts (2^48) 8524529665 10 Manual.Count131072.C065007.packed 64 cuts65007 = true := by
 decide +kernel
def pointBounds65007 : List (Nat × Nat × Nat) := [(8524550144,114904768820221,114905157795041)]
theorem point_links_checked65007 : (cuts65007.take 1).map (fun c => (8524529665-1+2*2^10*c.k,114904738706560+c.lower,114905127681362+c.upper)) = pointBounds65007 := by
 decide +kernel
def cuts65008 : List PrefixCut := [⟨64,187710977,187711089⟩]
theorem checked65008 : checkPrefixCuts (2^48) 8524660737 10 Manual.Count131072.C065008.packed 64 cuts65008 = true := by
 decide +kernel
def cuts65009 : List PrefixCut := [⟨13,40051246,40051266⟩,
⟨64,188929777,188929885⟩]
theorem checked65009 : checkPrefixCuts (2^48) 8524791809 10 Manual.Count131072.C065009.packed 64 cuts65009 = true := by
 decide +kernel
def pointBounds65009 : List (Nat × Nat × Nat) := [(8524818432,114905159498737,114905548473785)]
theorem point_links_checked65009 : (cuts65009.take 1).map (fun c => (8524791809-1+2*2^10*c.k,114905119447491+c.lower,114905508422519+c.upper)) = pointBounds65009 := by
 decide +kernel
def cuts65010 : List PrefixCut := [⟨64,190346633,190346734⟩]
theorem checked65010 : checkPrefixCuts (2^48) 8524922881 10 Manual.Count131072.C065010.packed 64 cuts65010 = true := by
 decide +kernel
def cuts65011 : List PrefixCut := [⟨16,47280789,47280814⟩,
⟨64,189914466,189914578⟩]
theorem checked65011 : checkPrefixCuts (2^48) 8525053953 10 Manual.Count131072.C065011.packed 64 cuts65011 = true := by
 decide +kernel
def pointBounds65011 : List (Nat × Nat × Nat) := [(8525086720,114905546004690,114905934979952)]
theorem point_links_checked65011 : (cuts65011.take 1).map (fun c => (8525053953-1+2*2^10*c.k,114905498723901+c.lower,114905887699138+c.upper)) = pointBounds65011 := by
 decide +kernel
def cuts65012 : List PrefixCut := [⟨64,188987082,188987196⟩]
theorem checked65012 : checkPrefixCuts (2^48) 8525185025 10 Manual.Count131072.C065012.packed 64 cuts65012 = true := by
 decide +kernel
def cuts65013 : List PrefixCut := [⟨19,56259749,56259776⟩,
⟨64,189974673,189974778⟩]
theorem checked65013 : checkPrefixCuts (2^48) 8525316097 10 Manual.Count131072.C065013.packed 64 cuts65013 = true := by
 decide +kernel
def pointBounds65013 : List (Nat × Nat × Nat) := [(8525355008,114905933885198,114906322860688)]
theorem point_links_checked65013 : (cuts65013.take 1).map (fun c => (8525316097-1+2*2^10*c.k,114905877625449+c.lower,114906266600912+c.upper)) = pointBounds65013 := by
 decide +kernel
def cuts65014 : List PrefixCut := [⟨64,188420017,188420132⟩]
theorem checked65014 : checkPrefixCuts (2^48) 8525447169 10 Manual.Count131072.C065014.packed 64 cuts65014 = true := by
 decide +kernel
def cuts65015 : List PrefixCut := [⟨22,65931467,65931503⟩,
⟨64,189803757,189803864⟩]
theorem checked65015 : checkPrefixCuts (2^48) 8525578241 10 Manual.Count131072.C065015.packed 64 cuts65015 = true := by
 decide +kernel
def pointBounds65015 : List (Nat × Nat × Nat) := [(8525623296,114906321951606,114906710927325)]
theorem point_links_checked65015 : (cuts65015.take 1).map (fun c => (8525578241-1+2*2^10*c.k,114906256020139+c.lower,114906644995822+c.upper)) = pointBounds65015 := by
 decide +kernel
def cuts65016 : List PrefixCut := [⟨64,186730470,186730576⟩]
theorem checked65016 : checkPrefixCuts (2^48) 8525709313 10 Manual.Count131072.C065016.packed 64 cuts65016 = true := by
 decide +kernel
def cuts65017 : List PrefixCut := [⟨25,74182971,74183018⟩,
⟨64,190722306,190722423⟩]
theorem checked65017 : checkPrefixCuts (2^48) 8525840385 10 Manual.Count131072.C065017.packed 64 cuts65017 = true := by
 decide +kernel
def pointBounds65017 : List (Nat × Nat × Nat) := [(8525891584,114906706737337,114907095713280)]
theorem point_links_checked65017 : (cuts65017.take 1).map (fun c => (8525840385-1+2*2^10*c.k,114906632554366+c.lower,114907021530262+c.upper)) = pointBounds65017 := by
 decide +kernel
def cuts65018 : List PrefixCut := [⟨64,187087872,187087982⟩]
theorem checked65018 : checkPrefixCuts (2^48) 8525971457 10 Manual.Count131072.C065018.packed 64 cuts65018 = true := by
 decide +kernel
def cuts65019 : List PrefixCut := [⟨28,82698067,82698116⟩,
⟨64,187580200,187580311⟩]
theorem checked65019 : checkPrefixCuts (2^48) 8526102529 10 Manual.Count131072.C065019.packed 64 cuts65019 = true := by
 decide +kernel
def pointBounds65019 : List (Nat × Nat × Nat) := [(8526159872,114907093062611,114907482038783)]
theorem point_links_checked65019 : (cuts65019.take 1).map (fun c => (8526102529-1+2*2^10*c.k,114907010364544+c.lower,114907399340667+c.upper)) = pointBounds65019 := by
 decide +kernel
def cuts65020 : List PrefixCut := [⟨64,190218329,190218444⟩]
theorem checked65020 : checkPrefixCuts (2^48) 8526233601 10 Manual.Count131072.C065020.packed 64 cuts65020 = true := by
 decide +kernel
def cuts65021 : List PrefixCut := [⟨31,90783481,90783533⟩,
⟨64,189588165,189588273⟩]
theorem checked65021 : checkPrefixCuts (2^48) 8526364673 10 Manual.Count131072.C065021.packed 64 cuts65021 = true := by
 decide +kernel
def pointBounds65021 : List (Nat × Nat × Nat) := [(8526428160,114907478946554,114907867922955)]
theorem point_links_checked65021 : (cuts65021.take 1).map (fun c => (8526364673-1+2*2^10*c.k,114907388163073+c.lower,114907777139422+c.upper)) = pointBounds65021 := by
 decide +kernel
def cuts65022 : List PrefixCut := [⟨64,189123097,189123213⟩]
theorem checked65022 : checkPrefixCuts (2^48) 8526495745 10 Manual.Count131072.C065022.packed 64 cuts65022 = true := by
 decide +kernel
def cuts65023 : List PrefixCut := [⟨34,97547948,97548002⟩,
⟨64,187106505,187106613⟩]
theorem checked65023 : checkPrefixCuts (2^48) 8526626817 10 Manual.Count131072.C065023.packed 64 cuts65023 = true := by
 decide +kernel
def pointBounds65023 : List (Nat × Nat × Nat) := [(8526696448,114907864422283,114908253398910)]
theorem point_links_checked65023 : (cuts65023.take 1).map (fun c => (8526626817-1+2*2^10*c.k,114907766874335+c.lower,114908155850908+c.upper)) = pointBounds65023 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000156
