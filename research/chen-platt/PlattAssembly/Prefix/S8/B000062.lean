import PlattAssemblyKernel
import PlattCertificates.Count131072.C071984
import PlattCertificates.Count131072.C071985
import PlattCertificates.Count131072.C071986
import PlattCertificates.Count131072.C071987
import PlattCertificates.Count131072.C071988
import PlattCertificates.Count131072.C071989
import PlattCertificates.Count131072.C071990
import PlattCertificates.Count131072.C071991
import PlattCertificates.Count131072.C071992
import PlattCertificates.Count131072.C071993
import PlattCertificates.Count131072.C071994
import PlattCertificates.Count131072.C071995
import PlattCertificates.Count131072.C071996
import PlattCertificates.Count131072.C071997
import PlattCertificates.Count131072.C071998
import PlattCertificates.Count131072.C071999
import PlattCertificates.Count131072.C072000
import PlattCertificates.Count131072.C072001
import PlattCertificates.Count131072.C072002
import PlattCertificates.Count131072.C072003
import PlattCertificates.Count131072.C072004
import PlattCertificates.Count131072.C072005
import PlattCertificates.Count131072.C072006
import PlattCertificates.Count131072.C072007
import PlattCertificates.Count131072.C072008
import PlattCertificates.Count131072.C072009
import PlattCertificates.Count131072.C072010
import PlattCertificates.Count131072.C072011
import PlattCertificates.Count131072.C072012
import PlattCertificates.Count131072.C072013
import PlattCertificates.Count131072.C072014
import PlattCertificates.Count131072.C072015
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000062
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71984 : List PrefixCut := [⟨64,171108008,171108101⟩]
theorem checked71984 : checkPrefixCuts (2^48) 9439019009 10 Manual.Count131072.C071984.packed 64 cuts71984 = true := by
 decide +kernel
def cuts71985 : List PrefixCut := [⟨64,170598694,170598792⟩]
theorem checked71985 : checkPrefixCuts (2^48) 9439150081 10 Manual.Count131072.C071985.packed 64 cuts71985 = true := by
 decide +kernel
def cuts71986 : List PrefixCut := [⟨4,10287732,10287738⟩,
⟨64,169224619,169224723⟩]
theorem checked71986 : checkPrefixCuts (2^48) 9439281153 10 Manual.Count131072.C071986.packed 64 cuts71986 = true := by
 decide +kernel
def pointBounds71986 : List (Nat × Nat × Nat) := [(9439289344,116156695160186,116157084867984)]
theorem point_links_checked71986 : (cuts71986.take 1).map (fun c => (9439281153-1+2*2^10*c.k,116156684872454+c.lower,116157074580246+c.upper)) = pointBounds71986 := by
 decide +kernel
def cuts71987 : List PrefixCut := [⟨64,172055086,172055195⟩]
theorem checked71987 : checkPrefixCuts (2^48) 9439412225 10 Manual.Count131072.C071987.packed 64 cuts71987 = true := by
 decide +kernel
def cuts71988 : List PrefixCut := [⟨21,55552109,55552141⟩,
⟨64,170382856,170382961⟩]
theorem checked71988 : checkPrefixCuts (2^48) 9439543297 10 Manual.Count131072.C071988.packed 64 cuts71988 = true := by
 decide +kernel
def pointBounds71988 : List (Nat × Nat × Nat) := [(9439586304,116157081704268,116157471412305)]
theorem point_links_checked71988 : (cuts71988.take 1).map (fun c => (9439543297-1+2*2^10*c.k,116157026152159+c.lower,116157415860164+c.upper)) = pointBounds71988 := by
 decide +kernel
def cuts71989 : List PrefixCut := [⟨64,171901208,171901311⟩]
theorem checked71989 : checkPrefixCuts (2^48) 9439674369 10 Manual.Count131072.C071989.packed 64 cuts71989 = true := by
 decide +kernel
def cuts71990 : List PrefixCut := [⟨38,102006513,102006575⟩,
⟨64,171421748,171421850⟩]
theorem checked71990 : checkPrefixCuts (2^48) 9439805441 10 Manual.Count131072.C071990.packed 64 cuts71990 = true := by
 decide +kernel
def pointBounds71990 : List (Nat × Nat × Nat) := [(9439883264,116157470442736,116157860151011)]
theorem point_links_checked71990 : (cuts71990.take 1).map (fun c => (9439805441-1+2*2^10*c.k,116157368436223+c.lower,116157758144436+c.upper)) = pointBounds71990 := by
 decide +kernel
def cuts71991 : List PrefixCut := [⟨64,168258735,168258836⟩]
theorem checked71991 : checkPrefixCuts (2^48) 9439936513 10 Manual.Count131072.C071991.packed 64 cuts71991 = true := by
 decide +kernel
def cuts71992 : List PrefixCut := [⟨55,148070559,148070643⟩,
⟨64,171894070,171894165⟩]
theorem checked71992 : checkPrefixCuts (2^48) 9440067585 10 Manual.Count131072.C071992.packed 64 cuts71992 = true := by
 decide +kernel
def pointBounds71992 : List (Nat × Nat × Nat) := [(9440180224,116157856187265,116158245895765)]
theorem point_links_checked71992 : (cuts71992.take 1).map (fun c => (9440067585-1+2*2^10*c.k,116157708116706+c.lower,116158097825122+c.upper)) = pointBounds71992 := by
 decide +kernel
def cuts71993 : List PrefixCut := [⟨64,169655433,169655536⟩]
theorem checked71993 : checkPrefixCuts (2^48) 9440198657 10 Manual.Count131072.C071993.packed 64 cuts71993 = true := by
 decide +kernel
def cuts71994 : List PrefixCut := [⟨64,173558968,173559063⟩]
theorem checked71994 : checkPrefixCuts (2^48) 9440329729 10 Manual.Count131072.C071994.packed 64 cuts71994 = true := by
 decide +kernel
def cuts71995 : List PrefixCut := [⟨8,20841226,20841240⟩,
⟨64,171380027,171380129⟩]
theorem checked71995 : checkPrefixCuts (2^48) 9440460801 10 Manual.Count131072.C071995.packed 64 cuts71995 = true := by
 decide +kernel
def pointBounds71995 : List (Nat × Nat × Nat) := [(9440477184,116158244066403,116158633775126)]
theorem point_links_checked71995 : (cuts71995.take 1).map (fun c => (9440460801-1+2*2^10*c.k,116158223225177+c.lower,116158612933886+c.upper)) = pointBounds71995 := by
 decide +kernel
def cuts71996 : List PrefixCut := [⟨64,168753913,168754013⟩]
theorem checked71996 : checkPrefixCuts (2^48) 9440591873 10 Manual.Count131072.C071996.packed 64 cuts71996 = true := by
 decide +kernel
def cuts71997 : List PrefixCut := [⟨25,65712023,65712060⟩,
⟨64,168751577,168751671⟩]
theorem checked71997 : checkPrefixCuts (2^48) 9440722945 10 Manual.Count131072.C071997.packed 64 cuts71997 = true := by
 decide +kernel
def pointBounds71997 : List (Nat × Nat × Nat) := [(9440774144,116158629071140,116159018780088)]
theorem point_links_checked71997 : (cuts71997.take 1).map (fun c => (9440722945-1+2*2^10*c.k,116158563359117+c.lower,116158953068028+c.upper)) = pointBounds71997 := by
 decide +kernel
def cuts71998 : List PrefixCut := [⟨64,171730663,171730765⟩]
theorem checked71998 : checkPrefixCuts (2^48) 9440854017 10 Manual.Count131072.C071998.packed 64 cuts71998 = true := by
 decide +kernel
def cuts71999 : List PrefixCut := [⟨42,111325506,111325570⟩,
⟨64,169879813,169879912⟩]
theorem checked71999 : checkPrefixCuts (2^48) 9440985089 10 Manual.Count131072.C071999.packed 64 cuts71999 = true := by
 decide +kernel
def pointBounds71999 : List (Nat × Nat × Nat) := [(9441071104,116159015166863,116159404876034)]
theorem point_links_checked71999 : (cuts71999.take 1).map (fun c => (9440985089-1+2*2^10*c.k,116158903841357+c.lower,116159293550464+c.upper)) = pointBounds71999 := by
 decide +kernel
def cuts72000 : List PrefixCut := [⟨64,168863793,168863895⟩]
theorem checked72000 : checkPrefixCuts (2^48) 9441116161 10 Manual.Count131072.C072000.packed 64 cuts72000 = true := by
 decide +kernel
def cuts72001 : List PrefixCut := [⟨59,156608340,156608431⟩,
⟨64,169964528,169964627⟩]
theorem checked72001 : checkPrefixCuts (2^48) 9441247233 10 Manual.Count131072.C072001.packed 64 cuts72001 = true := by
 decide +kernel
def pointBounds72001 : List (Nat × Nat × Nat) := [(9441368064,116159399193303,116159788902702)]
theorem point_links_checked72001 : (cuts72001.take 1).map (fun c => (9441247233-1+2*2^10*c.k,116159242584963+c.lower,116159632294271+c.upper)) = pointBounds72001 := by
 decide +kernel
def cuts72002 : List PrefixCut := [⟨64,169306305,169306412⟩]
theorem checked72002 : checkPrefixCuts (2^48) 9441378305 10 Manual.Count131072.C072002.packed 64 cuts72002 = true := by
 decide +kernel
def cuts72003 : List PrefixCut := [⟨64,170585874,170585977⟩]
theorem checked72003 : checkPrefixCuts (2^48) 9441509377 10 Manual.Count131072.C072003.packed 64 cuts72003 = true := by
 decide +kernel
def cuts72004 : List PrefixCut := [⟨12,30944894,30944912⟩,
⟨64,168109120,168109219⟩]
theorem checked72004 : checkPrefixCuts (2^48) 9441640449 10 Manual.Count131072.C072004.packed 64 cuts72004 = true := by
 decide +kernel
def pointBounds72004 : List (Nat × Nat × Nat) := [(9441665024,116159783386564,116160173096199)]
theorem point_links_checked72004 : (cuts72004.take 1).map (fun c => (9441640449-1+2*2^10*c.k,116159752441670+c.lower,116160142151287+c.upper)) = pointBounds72004 := by
 decide +kernel
def cuts72005 : List PrefixCut := [⟨64,171892854,171892956⟩]
theorem checked72005 : checkPrefixCuts (2^48) 9441771521 10 Manual.Count131072.C072005.packed 64 cuts72005 = true := by
 decide +kernel
def cuts72006 : List PrefixCut := [⟨29,77449378,77449423⟩,
⟨64,169982557,169982657⟩]
theorem checked72006 : checkPrefixCuts (2^48) 9441902593 10 Manual.Count131072.C072006.packed 64 cuts72006 = true := by
 decide +kernel
def pointBounds72006 : List (Nat × Nat × Nat) := [(9441961984,116160169893022,116160559602885)]
theorem point_links_checked72006 : (cuts72006.take 1).map (fun c => (9441902593-1+2*2^10*c.k,116160092443644+c.lower,116160482153462+c.upper)) = pointBounds72006 := by
 decide +kernel
def cuts72007 : List PrefixCut := [⟨64,170009998,170010100⟩]
theorem checked72007 : checkPrefixCuts (2^48) 9442033665 10 Manual.Count131072.C072007.packed 64 cuts72007 = true := by
 decide +kernel
def cuts72008 : List PrefixCut := [⟨46,120642163,120642240⟩,
⟨64,168129595,168129701⟩]
theorem checked72008 : checkPrefixCuts (2^48) 9442164737 10 Manual.Count131072.C072008.packed 64 cuts72008 = true := by
 decide +kernel
def pointBounds72008 : List (Nat × Nat × Nat) := [(9442258944,116160553078362,116160942788459)]
theorem point_links_checked72008 : (cuts72008.take 1).map (fun c => (9442164737-1+2*2^10*c.k,116160432436199+c.lower,116160822146219+c.upper)) = pointBounds72008 := by
 decide +kernel
def cuts72009 : List PrefixCut := [⟨64,170720729,170720828⟩]
theorem checked72009 : checkPrefixCuts (2^48) 9442295809 10 Manual.Count131072.C072009.packed 64 cuts72009 = true := by
 decide +kernel
def cuts72010 : List PrefixCut := [⟨63,167856659,167856760⟩,
⟨64,170479867,170479970⟩]
theorem checked72010 : checkPrefixCuts (2^48) 9442426881 10 Manual.Count131072.C072010.packed 64 cuts72010 = true := by
 decide +kernel
def pointBounds72010 : List (Nat × Nat × Nat) := [(9442555904,116160939143182,116161328853508)]
theorem point_links_checked72010 : (cuts72010.take 1).map (fun c => (9442426881-1+2*2^10*c.k,116160771286523+c.lower,116161160996748+c.upper)) = pointBounds72010 := by
 decide +kernel
def cuts72011 : List PrefixCut := [⟨64,168659157,168659258⟩]
theorem checked72011 : checkPrefixCuts (2^48) 9442557953 10 Manual.Count131072.C072011.packed 64 cuts72011 = true := by
 decide +kernel
def cuts72012 : List PrefixCut := [⟨64,171220357,171220463⟩]
theorem checked72012 : checkPrefixCuts (2^48) 9442689025 10 Manual.Count131072.C072012.packed 64 cuts72012 = true := by
 decide +kernel
def cuts72013 : List PrefixCut := [⟨16,42476826,42476853⟩,
⟨64,169638144,169638251⟩]
theorem checked72013 : checkPrefixCuts (2^48) 9442820097 10 Manual.Count131072.C072013.packed 64 cuts72013 = true := by
 decide +kernel
def pointBounds72013 : List (Nat × Nat × Nat) := [(9442852864,116161324122730,116161713833292)]
theorem point_links_checked72013 : (cuts72013.take 1).map (fun c => (9442820097-1+2*2^10*c.k,116161281645904+c.lower,116161671356439+c.upper)) = pointBounds72013 := by
 decide +kernel
def cuts72014 : List PrefixCut := [⟨64,167310793,167310889⟩]
theorem checked72014 : checkPrefixCuts (2^48) 9442951169 10 Manual.Count131072.C072014.packed 64 cuts72014 = true := by
 decide +kernel
def cuts72015 : List PrefixCut := [⟨33,85279016,85279069⟩,
⟨64,168083453,168083548⟩]
theorem checked72015 : checkPrefixCuts (2^48) 9443082241 10 Manual.Count131072.C072015.packed 64 cuts72015 = true := by
 decide +kernel
def pointBounds72015 : List (Nat × Nat × Nat) := [(9443149824,116161703873857,116162093584648)]
theorem point_links_checked72015 : (cuts72015.take 1).map (fun c => (9443082241-1+2*2^10*c.k,116161618594841+c.lower,116162008305579+c.upper)) = pointBounds72015 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000062
