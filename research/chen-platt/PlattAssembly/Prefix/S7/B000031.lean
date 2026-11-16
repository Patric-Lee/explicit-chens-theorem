import PlattAssemblyKernel
import PlattCertificates.Count131072.C060992
import PlattCertificates.Count131072.C060993
import PlattCertificates.Count131072.C060994
import PlattCertificates.Count131072.C060995
import PlattCertificates.Count131072.C060996
import PlattCertificates.Count131072.C060997
import PlattCertificates.Count131072.C060998
import PlattCertificates.Count131072.C060999
import PlattCertificates.Count131072.C061000
import PlattCertificates.Count131072.C061001
import PlattCertificates.Count131072.C061002
import PlattCertificates.Count131072.C061003
import PlattCertificates.Count131072.C061004
import PlattCertificates.Count131072.C061005
import PlattCertificates.Count131072.C061006
import PlattCertificates.Count131072.C061007
import PlattCertificates.Count131072.C061008
import PlattCertificates.Count131072.C061009
import PlattCertificates.Count131072.C061010
import PlattCertificates.Count131072.C061011
import PlattCertificates.Count131072.C061012
import PlattCertificates.Count131072.C061013
import PlattCertificates.Count131072.C061014
import PlattCertificates.Count131072.C061015
import PlattCertificates.Count131072.C061016
import PlattCertificates.Count131072.C061017
import PlattCertificates.Count131072.C061018
import PlattCertificates.Count131072.C061019
import PlattCertificates.Count131072.C061020
import PlattCertificates.Count131072.C061021
import PlattCertificates.Count131072.C061022
import PlattCertificates.Count131072.C061023
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000031
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60992 : List PrefixCut := [⟨13,41104127,41104151⟩,
⟨64,200029385,200029499⟩]
theorem checked60992 : checkPrefixCuts (2^48) 7998275585 10 Manual.Count131072.C060992.packed 64 cuts60992 = true := by
 decide +kernel
def pointBounds60992 : List (Nat × Nat × Nat) := [(7998302208,114119252169629,114119640692602)]
theorem point_links_checked60992 : (cuts60992.take 1).map (fun c => (7998275585-1+2*2^10*c.k,114119211065502+c.lower,114119599588451+c.upper)) = pointBounds60992 := by
 decide +kernel
def cuts60993 : List PrefixCut := [⟨64,202489495,202489611⟩]
theorem checked60993 : checkPrefixCuts (2^48) 7998406657 10 Manual.Count131072.C060993.packed 64 cuts60993 = true := by
 decide +kernel
def cuts60994 : List PrefixCut := [⟨8,25442918,25442933⟩,
⟨64,201324894,201325014⟩]
theorem checked60994 : checkPrefixCuts (2^48) 7998537729 10 Manual.Count131072.C060994.packed 64 cuts60994 = true := by
 decide +kernel
def pointBounds60994 : List (Nat × Nat × Nat) := [(7998554112,114119639027300,114120027550494)]
theorem point_links_checked60994 : (cuts60994.take 1).map (fun c => (7998537729-1+2*2^10*c.k,114119613584382+c.lower,114120002107561+c.upper)) = pointBounds60994 := by
 decide +kernel
def cuts60995 : List PrefixCut := [⟨64,205825899,205826017⟩]
theorem checked60995 : checkPrefixCuts (2^48) 7998668801 10 Manual.Count131072.C060995.packed 64 cuts60995 = true := by
 decide +kernel
def cuts60996 : List PrefixCut := [⟨3,8586270,8586274⟩,
⟨64,197904907,197905020⟩]
theorem checked60996 : checkPrefixCuts (2^48) 7998799873 10 Manual.Count131072.C060996.packed 64 cuts60996 = true := by
 decide +kernel
def pointBounds60996 : List (Nat × Nat × Nat) := [(7998806016,114120029321445,114120417844866)]
theorem point_links_checked60996 : (cuts60996.take 1).map (fun c => (7998799873-1+2*2^10*c.k,114120020735175+c.lower,114120409258592+c.upper)) = pointBounds60996 := by
 decide +kernel
def cuts60997 : List PrefixCut := [⟨62,195473713,195473823⟩,
⟨64,201913208,201913322⟩]
theorem checked60997 : checkPrefixCuts (2^48) 7998930945 10 Manual.Count131072.C060997.packed 64 cuts60997 = true := by
 decide +kernel
def pointBounds60997 : List (Nat × Nat × Nat) := [(7999057920,114120414113795,114120802637435)]
theorem point_links_checked60997 : (cuts60997.take 1).map (fun c => (7998930945-1+2*2^10*c.k,114120218640082+c.lower,114120607163612+c.upper)) = pointBounds60997 := by
 decide +kernel
def cuts60998 : List PrefixCut := [⟨64,202191393,202191513⟩]
theorem checked60998 : checkPrefixCuts (2^48) 7999062017 10 Manual.Count131072.C060998.packed 64 cuts60998 = true := by
 decide +kernel
def cuts60999 : List PrefixCut := [⟨57,179316281,179316389⟩,
⟨64,201730633,201730755⟩]
theorem checked60999 : checkPrefixCuts (2^48) 7999193089 10 Manual.Count131072.C060999.packed 64 cuts60999 = true := by
 decide +kernel
def pointBounds60999 : List (Nat × Nat × Nat) := [(7999309824,114120802060964,114121190584836)]
theorem point_links_checked60999 : (cuts60999.take 1).map (fun c => (7999193089-1+2*2^10*c.k,114120622744683+c.lower,114121011268447+c.upper)) = pointBounds60999 := by
 decide +kernel
def cuts61000 : List PrefixCut := [⟨64,201445851,201445967⟩]
theorem checked61000 : checkPrefixCuts (2^48) 7999324161 10 Manual.Count131072.C061000.packed 64 cuts61000 = true := by
 decide +kernel
def cuts61001 : List PrefixCut := [⟨52,163054365,163054458⟩,
⟨64,201618479,201618595⟩]
theorem checked61001 : checkPrefixCuts (2^48) 7999455233 10 Manual.Count131072.C061001.packed 64 cuts61001 = true := by
 decide +kernel
def pointBounds61001 : List (Nat × Nat × Nat) := [(7999561728,114121188975532,114121577499627)]
theorem point_links_checked61001 : (cuts61001.take 1).map (fun c => (7999455233-1+2*2^10*c.k,114121025921167+c.lower,114121414445169+c.upper)) = pointBounds61001 := by
 decide +kernel
def cuts61002 : List PrefixCut := [⟨64,204183733,204183853⟩]
theorem checked61002 : checkPrefixCuts (2^48) 7999586305 10 Manual.Count131072.C061002.packed 64 cuts61002 = true := by
 decide +kernel
def cuts61003 : List PrefixCut := [⟨47,148552736,148552822⟩,
⟨64,202772983,202773099⟩]
theorem checked61003 : checkPrefixCuts (2^48) 7999717377 10 Manual.Count131072.C061003.packed 64 cuts61003 = true := by
 decide +kernel
def pointBounds61003 : List (Nat × Nat × Nat) := [(7999813632,114121580276115,114121968800439)]
theorem point_links_checked61003 : (cuts61003.take 1).map (fun c => (7999717377-1+2*2^10*c.k,114121431723379+c.lower,114121820247617+c.upper)) = pointBounds61003 := by
 decide +kernel
def cuts61004 : List PrefixCut := [⟨64,202945574,202945689⟩]
theorem checked61004 : checkPrefixCuts (2^48) 7999848449 10 Manual.Count131072.C061004.packed 64 cuts61004 = true := by
 decide +kernel
def cuts61005 : List PrefixCut := [⟨42,133383544,133383619⟩,
⟨64,201429347,201429463⟩]
theorem checked61005 : checkPrefixCuts (2^48) 7999979521 10 Manual.Count131072.C061005.packed 64 cuts61005 = true := by
 decide +kernel
def pointBounds61005 : List (Nat × Nat × Nat) := [(8000065536,114121970825480,114122359350024)]
theorem point_links_checked61005 : (cuts61005.take 1).map (fun c => (7999979521-1+2*2^10*c.k,114121837441936+c.lower,114122225966405+c.upper)) = pointBounds61005 := by
 decide +kernel
def cuts61006 : List PrefixCut := [⟨64,200792747,200792865⟩]
theorem checked61006 : checkPrefixCuts (2^48) 8000110593 10 Manual.Count131072.C061006.packed 64 cuts61006 = true := by
 decide +kernel
def cuts61007 : List PrefixCut := [⟨37,117617212,117617277⟩,
⟨64,204378105,204378220⟩]
theorem checked61007 : checkPrefixCuts (2^48) 8000241665 10 Manual.Count131072.C061007.packed 64 cuts61007 = true := by
 decide +kernel
def pointBounds61007 : List (Nat × Nat × Nat) := [(8000317440,114122357281242,114122745806010)]
theorem point_links_checked61007 : (cuts61007.take 1).map (fun c => (8000241665-1+2*2^10*c.k,114122239664030+c.lower,114122628188733+c.upper)) = pointBounds61007 := by
 decide +kernel
def cuts61008 : List PrefixCut := [⟨64,200821334,200821447⟩]
theorem checked61008 : checkPrefixCuts (2^48) 8000372737 10 Manual.Count131072.C061008.packed 64 cuts61008 = true := by
 decide +kernel
def cuts61009 : List PrefixCut := [⟨32,100374250,100374311⟩,
⟨64,201029135,201029256⟩]
theorem checked61009 : checkPrefixCuts (2^48) 8000503809 10 Manual.Count131072.C061009.packed 64 cuts61009 = true := by
 decide +kernel
def pointBounds61009 : List (Nat × Nat × Nat) := [(8000569344,114122745237719,114123133762711)]
theorem point_links_checked61009 : (cuts61009.take 1).map (fun c => (8000503809-1+2*2^10*c.k,114122644863469+c.lower,114123033388400+c.upper)) = pointBounds61009 := by
 decide +kernel
def cuts61010 : List PrefixCut := [⟨64,201729481,201729592⟩]
theorem checked61010 : checkPrefixCuts (2^48) 8000634881 10 Manual.Count131072.C061010.packed 64 cuts61010 = true := by
 decide +kernel
def cuts61011 : List PrefixCut := [⟨27,86931934,86931984⟩,
⟨64,204399897,204400013⟩]
theorem checked61011 : checkPrefixCuts (2^48) 8000765953 10 Manual.Count131072.C061011.packed 64 cuts61011 = true := by
 decide +kernel
def pointBounds61011 : List (Nat × Nat × Nat) := [(8000821248,114123134554019,114123523079232)]
theorem point_links_checked61011 : (cuts61011.take 1).map (fun c => (8000765953-1+2*2^10*c.k,114123047622085+c.lower,114123436147248+c.upper)) = pointBounds61011 := by
 decide +kernel
def cuts61012 : List PrefixCut := [⟨64,202637536,202637646⟩]
theorem checked61012 : checkPrefixCuts (2^48) 8000897025 10 Manual.Count131072.C061012.packed 64 cuts61012 = true := by
 decide +kernel
def cuts61013 : List PrefixCut := [⟨22,70465024,70465064⟩,
⟨64,204076589,204076704⟩]
theorem checked61013 : checkPrefixCuts (2^48) 8001028097 10 Manual.Count131072.C061013.packed 64 cuts61013 = true := by
 decide +kernel
def pointBounds61013 : List (Nat × Nat × Nat) := [(8001073152,114123525124542,114123913649971)]
theorem point_links_checked61013 : (cuts61013.take 1).map (fun c => (8001028097-1+2*2^10*c.k,114123454659518+c.lower,114123843184907+c.upper)) = pointBounds61013 := by
 decide +kernel
def cuts61014 : List PrefixCut := [⟨64,202771610,202771725⟩]
theorem checked61014 : checkPrefixCuts (2^48) 8001159169 10 Manual.Count131072.C061014.packed 64 cuts61014 = true := by
 decide +kernel
def cuts61015 : List PrefixCut := [⟨17,52697562,52697595⟩,
⟨64,199144920,199145043⟩]
theorem checked61015 : checkPrefixCuts (2^48) 8001290241 10 Manual.Count131072.C061015.packed 64 cuts61015 = true := by
 decide +kernel
def pointBounds61015 : List (Nat × Nat × Nat) := [(8001325056,114123914205279,114124302730931)]
theorem point_links_checked61015 : (cuts61015.take 1).map (fun c => (8001290241-1+2*2^10*c.k,114123861507717+c.lower,114124250033336+c.upper)) = pointBounds61015 := by
 decide +kernel
def cuts61016 : List PrefixCut := [⟨64,204066571,204066683⟩]
theorem checked61016 : checkPrefixCuts (2^48) 8001421313 10 Manual.Count131072.C061016.packed 64 cuts61016 = true := by
 decide +kernel
def cuts61017 : List PrefixCut := [⟨12,39680200,39680224⟩,
⟨64,201987774,201987888⟩]
theorem checked61017 : checkPrefixCuts (2^48) 8001552385 10 Manual.Count131072.C061017.packed 64 cuts61017 = true := by
 decide +kernel
def pointBounds61017 : List (Nat × Nat × Nat) := [(8001576960,114124304399408,114124692925286)]
theorem point_links_checked61017 : (cuts61017.take 1).map (fun c => (8001552385-1+2*2^10*c.k,114124264719208+c.lower,114124653245062+c.upper)) = pointBounds61017 := by
 decide +kernel
def cuts61018 : List PrefixCut := [⟨64,201527146,201527264⟩]
theorem checked61018 : checkPrefixCuts (2^48) 8001683457 10 Manual.Count131072.C061018.packed 64 cuts61018 = true := by
 decide +kernel
def cuts61019 : List PrefixCut := [⟨7,22407335,22407349⟩,
⟨64,203001248,203001364⟩]
theorem checked61019 : checkPrefixCuts (2^48) 8001814529 10 Manual.Count131072.C061019.packed 64 cuts61019 = true := by
 decide +kernel
def pointBounds61019 : List (Nat × Nat × Nat) := [(8001828864,114124690641463,114125079167563)]
theorem point_links_checked61019 : (cuts61019.take 1).map (fun c => (8001814529-1+2*2^10*c.k,114124668234128+c.lower,114125056760214+c.upper)) = pointBounds61019 := by
 decide +kernel
def cuts61020 : List PrefixCut := [⟨64,204545646,204545761⟩]
theorem checked61020 : checkPrefixCuts (2^48) 8001945601 10 Manual.Count131072.C061020.packed 64 cuts61020 = true := by
 decide +kernel
def cuts61021 : List PrefixCut := [⟨2,5663210,5663214⟩,
⟨64,199160519,199160632⟩]
theorem checked61021 : checkPrefixCuts (2^48) 8002076673 10 Manual.Count131072.C061021.packed 64 cuts61021 = true := by
 decide +kernel
def pointBounds61021 : List (Nat × Nat × Nat) := [(8002080768,114125081444232,114125469970553)]
theorem point_links_checked61021 : (cuts61021.take 1).map (fun c => (8002076673-1+2*2^10*c.k,114125075781022+c.lower,114125464307339+c.upper)) = pointBounds61021 := by
 decide +kernel
def cuts61022 : List PrefixCut := [⟨61,190926543,190926652⟩,
⟨64,199825589,199825702⟩]
theorem checked61022 : checkPrefixCuts (2^48) 8002207745 10 Manual.Count131072.C061022.packed 64 cuts61022 = true := by
 decide +kernel
def pointBounds61022 : List (Nat × Nat × Nat) := [(8002332672,114125465868084,114125854394623)]
theorem point_links_checked61022 : (cuts61022.take 1).map (fun c => (8002207745-1+2*2^10*c.k,114125274941541+c.lower,114125663467971+c.upper)) = pointBounds61022 := by
 decide +kernel
def cuts61023 : List PrefixCut := [⟨64,204183863,204183981⟩]
theorem checked61023 : checkPrefixCuts (2^48) 8002338817 10 Manual.Count131072.C061023.packed 64 cuts61023 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000031
