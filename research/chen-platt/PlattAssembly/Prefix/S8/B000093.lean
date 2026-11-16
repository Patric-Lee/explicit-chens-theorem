import PlattAssemblyKernel
import PlattCertificates.Count131072.C072976
import PlattCertificates.Count131072.C072977
import PlattCertificates.Count131072.C072978
import PlattCertificates.Count131072.C072979
import PlattCertificates.Count131072.C072980
import PlattCertificates.Count131072.C072981
import PlattCertificates.Count131072.C072982
import PlattCertificates.Count131072.C072983
import PlattCertificates.Count131072.C072984
import PlattCertificates.Count131072.C072985
import PlattCertificates.Count131072.C072986
import PlattCertificates.Count131072.C072987
import PlattCertificates.Count131072.C072988
import PlattCertificates.Count131072.C072989
import PlattCertificates.Count131072.C072990
import PlattCertificates.Count131072.C072991
import PlattCertificates.Count131072.C072992
import PlattCertificates.Count131072.C072993
import PlattCertificates.Count131072.C072994
import PlattCertificates.Count131072.C072995
import PlattCertificates.Count131072.C072996
import PlattCertificates.Count131072.C072997
import PlattCertificates.Count131072.C072998
import PlattCertificates.Count131072.C072999
import PlattCertificates.Count131072.C073000
import PlattCertificates.Count131072.C073001
import PlattCertificates.Count131072.C073002
import PlattCertificates.Count131072.C073003
import PlattCertificates.Count131072.C073004
import PlattCertificates.Count131072.C073005
import PlattCertificates.Count131072.C073006
import PlattCertificates.Count131072.C073007
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000093
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts72976 : List PrefixCut := [⟨64,167841737,167841841⟩]
theorem checked72976 : checkPrefixCuts (2^48) 9569042433 10 Manual.Count131072.C072976.packed 64 cuts72976 = true := by
 decide +kernel
def cuts72977 : List PrefixCut := [⟨25,65035847,65035889⟩,
⟨64,167221731,167221836⟩]
theorem checked72977 : checkPrefixCuts (2^48) 9569173505 10 Manual.Count131072.C072977.packed 64 cuts72977 = true := by
 decide +kernel
def pointBounds72977 : List (Nat × Nat × Nat) := [(9569224704,116324170872266,116324560679710)]
theorem point_links_checked72977 : (cuts72977.take 1).map (fun c => (9569173505-1+2*2^10*c.k,116324105836419+c.lower,116324495643821+c.upper)) = pointBounds72977 := by
 decide +kernel
def cuts72978 : List PrefixCut := [⟨64,167278271,167278374⟩]
theorem checked72978 : checkPrefixCuts (2^48) 9569304577 10 Manual.Count131072.C072978.packed 64 cuts72978 = true := by
 decide +kernel
def cuts72979 : List PrefixCut := [⟨44,115861011,115861073⟩,
⟨64,168658439,168658535⟩]
theorem checked72979 : checkPrefixCuts (2^48) 9569435649 10 Manual.Count131072.C072979.packed 64 cuts72979 = true := by
 decide +kernel
def pointBounds72979 : List (Nat × Nat × Nat) := [(9569525760,116324556197432,116324946005104)]
theorem point_links_checked72979 : (cuts72979.take 1).map (fun c => (9569435649-1+2*2^10*c.k,116324440336421+c.lower,116324830144031+c.upper)) = pointBounds72979 := by
 decide +kernel
def cuts72980 : List PrefixCut := [⟨64,165950082,165950179⟩]
theorem checked72980 : checkPrefixCuts (2^48) 9569566721 10 Manual.Count131072.C072980.packed 64 cuts72980 = true := by
 decide +kernel
def cuts72981 : List PrefixCut := [⟨63,167800845,167800949⟩,
⟨64,170447992,170448097⟩]
theorem checked72981 : checkPrefixCuts (2^48) 9569697793 10 Manual.Count131072.C072981.packed 64 cuts72981 = true := by
 decide +kernel
def pointBounds72981 : List (Nat × Nat × Nat) := [(9569826816,116324942745787,116325332553694)]
theorem point_links_checked72981 : (cuts72981.take 1).map (fun c => (9569697793-1+2*2^10*c.k,116324774944942+c.lower,116325164752745+c.upper)) = pointBounds72981 := by
 decide +kernel
def cuts72982 : List PrefixCut := [⟨64,167386756,167386852⟩]
theorem checked72982 : checkPrefixCuts (2^48) 9569828865 10 Manual.Count131072.C072982.packed 64 cuts72982 = true := by
 decide +kernel
def cuts72983 : List PrefixCut := [⟨64,167855065,167855165⟩]
theorem checked72983 : checkPrefixCuts (2^48) 9569959937 10 Manual.Count131072.C072983.packed 64 cuts72983 = true := by
 decide +kernel
def cuts72984 : List PrefixCut := [⟨18,46882533,46882563⟩,
⟨64,167617467,167617569⟩]
theorem checked72984 : checkPrefixCuts (2^48) 9570091009 10 Manual.Count131072.C072984.packed 64 cuts72984 = true := by
 decide +kernel
def pointBounds72984 : List (Nat × Nat × Nat) := [(9570127872,116325327517288,116325717325422)]
theorem point_links_checked72984 : (cuts72984.take 1).map (fun c => (9570091009-1+2*2^10*c.k,116325280634755+c.lower,116325670442859+c.upper)) = pointBounds72984 := by
 decide +kernel
def cuts72985 : List PrefixCut := [⟨64,168115177,168115277⟩]
theorem checked72985 : checkPrefixCuts (2^48) 9570222081 10 Manual.Count131072.C072985.packed 64 cuts72985 = true := by
 decide +kernel
def cuts72986 : List PrefixCut := [⟨37,96438706,96438769⟩,
⟨64,168436372,168436478⟩]
theorem checked72986 : checkPrefixCuts (2^48) 9570353153 10 Manual.Count131072.C072986.packed 64 cuts72986 = true := by
 decide +kernel
def pointBounds72986 : List (Nat × Nat × Nat) := [(9570428928,116325712806105,116326102614474)]
theorem point_links_checked72986 : (cuts72986.take 1).map (fun c => (9570353153-1+2*2^10*c.k,116325616367399+c.lower,116326006175705+c.upper)) = pointBounds72986 := by
 decide +kernel
def cuts72987 : List PrefixCut := [⟨64,168992880,168992982⟩]
theorem checked72987 : checkPrefixCuts (2^48) 9570484225 10 Manual.Count131072.C072987.packed 64 cuts72987 = true := by
 decide +kernel
def cuts72988 : List PrefixCut := [⟨56,145227297,145227388⟩,
⟨64,166402458,166402562⟩]
theorem checked72988 : checkPrefixCuts (2^48) 9570615297 10 Manual.Count131072.C072988.packed 64 cuts72988 = true := by
 decide +kernel
def pointBounds72988 : List (Nat × Nat × Nat) := [(9570729984,116326099023948,116326488832553)]
theorem point_links_checked72988 : (cuts72988.take 1).map (fun c => (9570615297-1+2*2^10*c.k,116325953796651+c.lower,116326343605165+c.upper)) = pointBounds72988 := by
 decide +kernel
def cuts72989 : List PrefixCut := [⟨64,170047013,170047110⟩]
theorem checked72989 : checkPrefixCuts (2^48) 9570746369 10 Manual.Count131072.C072989.packed 64 cuts72989 = true := by
 decide +kernel
def cuts72990 : List PrefixCut := [⟨64,167162554,167162651⟩]
theorem checked72990 : checkPrefixCuts (2^48) 9570877441 10 Manual.Count131072.C072990.packed 64 cuts72990 = true := by
 decide +kernel
def cuts72991 : List PrefixCut := [⟨11,29144401,29144416⟩,
⟨64,169748252,169748353⟩]
theorem checked72991 : checkPrefixCuts (2^48) 9571008513 10 Manual.Count131072.C072991.packed 64 cuts72991 = true := by
 decide +kernel
def pointBounds72991 : List (Nat × Nat × Nat) := [(9571031040,116326486553077,116326876361904)]
theorem point_links_checked72991 : (cuts72991.take 1).map (fun c => (9571008513-1+2*2^10*c.k,116326457408676+c.lower,116326847217488+c.upper)) = pointBounds72991 := by
 decide +kernel
def cuts72992 : List PrefixCut := [⟨64,167157973,167158080⟩]
theorem checked72992 : checkPrefixCuts (2^48) 9571139585 10 Manual.Count131072.C072992.packed 64 cuts72992 = true := by
 decide +kernel
def cuts72993 : List PrefixCut := [⟨30,78019993,78020042⟩,
⟨64,167832069,167832170⟩]
theorem checked72993 : checkPrefixCuts (2^48) 9571270657 10 Manual.Count131072.C072993.packed 64 cuts72993 = true := by
 decide +kernel
def pointBounds72993 : List (Nat × Nat × Nat) := [(9571332096,116326872334894,116327262143963)]
theorem point_links_checked72993 : (cuts72993.take 1).map (fun c => (9571270657-1+2*2^10*c.k,116326794314901+c.lower,116327184123921+c.upper)) = pointBounds72993 := by
 decide +kernel
def cuts72994 : List PrefixCut := [⟨64,167859182,167859281⟩]
theorem checked72994 : checkPrefixCuts (2^48) 9571401729 10 Manual.Count131072.C072994.packed 64 cuts72994 = true := by
 decide +kernel
def cuts72995 : List PrefixCut := [⟨49,126069306,126069381⟩,
⟨64,165269035,165269133⟩]
theorem checked72995 : checkPrefixCuts (2^48) 9571532801 10 Manual.Count131072.C072995.packed 64 cuts72995 = true := by
 decide +kernel
def pointBounds72995 : List (Nat × Nat × Nat) := [(9571633152,116327256075458,116327645884753)]
theorem point_links_checked72995 : (cuts72995.take 1).map (fun c => (9571532801-1+2*2^10*c.k,116327130006152+c.lower,116327519815372+c.upper)) = pointBounds72995 := by
 decide +kernel
def cuts72996 : List PrefixCut := [⟨64,164972713,164972804⟩]
theorem checked72996 : checkPrefixCuts (2^48) 9571663873 10 Manual.Count131072.C072996.packed 64 cuts72996 = true := by
 decide +kernel
def cuts72997 : List PrefixCut := [⟨64,168116956,168117056⟩]
theorem checked72997 : checkPrefixCuts (2^48) 9571794945 10 Manual.Count131072.C072997.packed 64 cuts72997 = true := by
 decide +kernel
def cuts72998 : List PrefixCut := [⟨4,10615668,10615675⟩,
⟨64,165409298,165409393⟩]
theorem checked72998 : checkPrefixCuts (2^48) 9571926017 10 Manual.Count131072.C072998.packed 64 cuts72998 = true := by
 decide +kernel
def pointBounds72998 : List (Nat × Nat × Nat) := [(9571934208,116327638980524,116328028790040)]
theorem point_links_checked72998 : (cuts72998.take 1).map (fun c => (9571926017-1+2*2^10*c.k,116327628364856+c.lower,116328018174365+c.upper)) = pointBounds72998 := by
 decide +kernel
def cuts72999 : List PrefixCut := [⟨64,169053331,169053425⟩]
theorem checked72999 : checkPrefixCuts (2^48) 9572057089 10 Manual.Count131072.C072999.packed 64 cuts72999 = true := by
 decide +kernel
def cuts73000 : List PrefixCut := [⟨23,59428356,59428390⟩,
⟨64,167257285,167257388⟩]
theorem checked73000 : checkPrefixCuts (2^48) 9572188161 10 Manual.Count131072.C073000.packed 64 cuts73000 = true := by
 decide +kernel
def pointBounds73000 : List (Nat × Nat × Nat) := [(9572235264,116328022255841,116328412065573)]
theorem point_links_checked73000 : (cuts73000.take 1).map (fun c => (9572188161-1+2*2^10*c.k,116327962827485+c.lower,116328352637183+c.upper)) = pointBounds73000 := by
 decide +kernel
def cuts73001 : List PrefixCut := [⟨64,167666669,167666765⟩]
theorem checked73001 : checkPrefixCuts (2^48) 9572319233 10 Manual.Count131072.C073001.packed 64 cuts73001 = true := by
 decide +kernel
def cuts73002 : List PrefixCut := [⟨42,107885304,107885373⟩,
⟨64,166341158,166341260⟩]
theorem checked73002 : checkPrefixCuts (2^48) 9572450305 10 Manual.Count131072.C073002.packed 64 cuts73002 = true := by
 decide +kernel
def pointBounds73002 : List (Nat × Nat × Nat) := [(9572536320,116328405636743,116328795446709)]
theorem point_links_checked73002 : (cuts73002.take 1).map (fun c => (9572450305-1+2*2^10*c.k,116328297751439+c.lower,116328687561336+c.upper)) = pointBounds73002 := by
 decide +kernel
def cuts73003 : List PrefixCut := [⟨64,167191611,167191710⟩]
theorem checked73003 : checkPrefixCuts (2^48) 9572581377 10 Manual.Count131072.C073003.packed 64 cuts73003 = true := by
 decide +kernel
def cuts73004 : List PrefixCut := [⟨61,159985466,159985565⟩,
⟨64,168100829,168100932⟩]
theorem checked73004 : checkPrefixCuts (2^48) 9572712449 10 Manual.Count131072.C073004.packed 64 cuts73004 = true := by
 decide +kernel
def pointBounds73004 : List (Nat × Nat × Nat) := [(9572837376,116328791269674,116329181079871)]
theorem point_links_checked73004 : (cuts73004.take 1).map (fun c => (9572712449-1+2*2^10*c.k,116328631284208+c.lower,116329021094306+c.upper)) = pointBounds73004 := by
 decide +kernel
def cuts73005 : List PrefixCut := [⟨64,167686888,167686982⟩]
theorem checked73005 : checkPrefixCuts (2^48) 9572843521 10 Manual.Count131072.C073005.packed 64 cuts73005 = true := by
 decide +kernel
def cuts73006 : List PrefixCut := [⟨64,169654584,169654688⟩]
theorem checked73006 : checkPrefixCuts (2^48) 9572974593 10 Manual.Count131072.C073006.packed 64 cuts73006 = true := by
 decide +kernel
def cuts73007 : List PrefixCut := [⟨16,42574999,42575025⟩,
⟨64,168887803,168887904⟩]
theorem checked73007 : checkPrefixCuts (2^48) 9573105665 10 Manual.Count131072.C073007.packed 64 cuts73007 = true := by
 decide +kernel
def pointBounds73007 : List (Nat × Nat × Nat) := [(9573138432,116329179301508,116329569111933)]
theorem point_links_checked73007 : (cuts73007.take 1).map (fun c => (9573105665-1+2*2^10*c.k,116329136726509+c.lower,116329526536908+c.upper)) = pointBounds73007 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000093
