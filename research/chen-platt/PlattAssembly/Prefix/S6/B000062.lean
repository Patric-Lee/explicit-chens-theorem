import PlattAssemblyKernel
import PlattCertificates.Count131072.C051984
import PlattCertificates.Count131072.C051985
import PlattCertificates.Count131072.C051986
import PlattCertificates.Count131072.C051987
import PlattCertificates.Count131072.C051988
import PlattCertificates.Count131072.C051989
import PlattCertificates.Count131072.C051990
import PlattCertificates.Count131072.C051991
import PlattCertificates.Count131072.C051992
import PlattCertificates.Count131072.C051993
import PlattCertificates.Count131072.C051994
import PlattCertificates.Count131072.C051995
import PlattCertificates.Count131072.C051996
import PlattCertificates.Count131072.C051997
import PlattCertificates.Count131072.C051998
import PlattCertificates.Count131072.C051999
import PlattCertificates.Count131072.C052000
import PlattCertificates.Count131072.C052001
import PlattCertificates.Count131072.C052002
import PlattCertificates.Count131072.C052003
import PlattCertificates.Count131072.C052004
import PlattCertificates.Count131072.C052005
import PlattCertificates.Count131072.C052006
import PlattCertificates.Count131072.C052007
import PlattCertificates.Count131072.C052008
import PlattCertificates.Count131072.C052009
import PlattCertificates.Count131072.C052010
import PlattCertificates.Count131072.C052011
import PlattCertificates.Count131072.C052012
import PlattCertificates.Count131072.C052013
import PlattCertificates.Count131072.C052014
import PlattCertificates.Count131072.C052015
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000062
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts51984 : List PrefixCut := [⟨64,240244635,240244768⟩]
theorem checked51984 : checkPrefixCuts (2^48) 6817579009 10 Manual.Count131072.C051984.packed 64 cuts51984 = true := by
 decide +kernel
def cuts51985 : List PrefixCut := [⟨4,15234466,15234474⟩,
⟨64,242634568,242634706⟩]
theorem checked51985 : checkPrefixCuts (2^48) 6817710081 10 Manual.Count131072.C051985.packed 64 cuts51985 = true := by
 decide +kernel
def pointBounds51985 : List (Nat × Nat × Nat) := [(6817718272,112140983414887,112141370812208)]
theorem point_links_checked51985 : (cuts51985.take 1).map (fun c => (6817710081-1+2*2^10*c.k,112140968180421+c.lower,112141355577734+c.upper)) = pointBounds51985 := by
 decide +kernel
def cuts51986 : List PrefixCut := [⟨45,166088616,166088711⟩,
⟨64,236643604,236643738⟩]
theorem checked51986 : checkPrefixCuts (2^48) 6817841153 10 Manual.Count131072.C051986.packed 64 cuts51986 = true := by
 decide +kernel
def pointBounds51986 : List (Nat × Nat × Nat) := [(6817933312,112141376903605,112141764301151)]
theorem point_links_checked51986 : (cuts51986.take 1).map (fun c => (6817841153-1+2*2^10*c.k,112141210814989+c.lower,112141598212440+c.upper)) = pointBounds51986 := by
 decide +kernel
def cuts51987 : List PrefixCut := [⟨64,240973873,240974009⟩]
theorem checked51987 : checkPrefixCuts (2^48) 6817972225 10 Manual.Count131072.C051987.packed 64 cuts51987 = true := by
 decide +kernel
def cuts51988 : List PrefixCut := [⟨22,80172221,80172265⟩,
⟨64,235272173,235272308⟩]
theorem checked51988 : checkPrefixCuts (2^48) 6818103297 10 Manual.Count131072.C051988.packed 64 cuts51988 = true := by
 decide +kernel
def pointBounds51988 : List (Nat × Nat × Nat) := [(6818148352,112141768604687,112142156002452)]
theorem point_links_checked51988 : (cuts51988.take 1).map (fun c => (6818103297-1+2*2^10*c.k,112141688432466+c.lower,112142075830187+c.upper)) = pointBounds51988 := by
 decide +kernel
def cuts51989 : List PrefixCut := [⟨63,237290513,237290645⟩,
⟨64,240923318,240923452⟩]
theorem checked51989 : checkPrefixCuts (2^48) 6818234369 10 Manual.Count131072.C051989.packed 64 cuts51989 = true := by
 decide +kernel
def pointBounds51989 : List (Nat × Nat × Nat) := [(6818363392,112142160995152,112142548393140)]
theorem point_links_checked51989 : (cuts51989.take 1).map (fun c => (6818234369-1+2*2^10*c.k,112141923704639+c.lower,112142311102495+c.upper)) = pointBounds51989 := by
 decide +kernel
def cuts51990 : List PrefixCut := [⟨64,238813343,238813478⟩]
theorem checked51990 : checkPrefixCuts (2^48) 6818365441 10 Manual.Count131072.C051990.packed 64 cuts51990 = true := by
 decide +kernel
def cuts51991 : List PrefixCut := [⟨40,149808138,149808225⟩,
⟨64,239840766,239840901⟩]
theorem checked51991 : checkPrefixCuts (2^48) 6818496513 10 Manual.Count131072.C051991.packed 64 cuts51991 = true := by
 decide +kernel
def pointBounds51991 : List (Nat × Nat × Nat) := [(6818578432,112142553249438,112142940647650)]
theorem point_links_checked51991 : (cuts51991.take 1).map (fun c => (6818496513-1+2*2^10*c.k,112142403441300+c.lower,112142790839425+c.upper)) = pointBounds51991 := by
 decide +kernel
def cuts51992 : List PrefixCut := [⟨64,238226227,238226360⟩]
theorem checked51992 : checkPrefixCuts (2^48) 6818627585 10 Manual.Count131072.C051992.packed 64 cuts51992 = true := by
 decide +kernel
def cuts51993 : List PrefixCut := [⟨17,66418539,66418575⟩,
⟨64,242556008,242556142⟩]
theorem checked51993 : checkPrefixCuts (2^48) 6818758657 10 Manual.Count131072.C051993.packed 64 cuts51993 = true := by
 decide +kernel
def pointBounds51993 : List (Nat × Nat × Nat) := [(6818793472,112142947926832,112143335325261)]
theorem point_links_checked51993 : (cuts51993.take 1).map (fun c => (6818758657-1+2*2^10*c.k,112142881508293+c.lower,112143268906686+c.upper)) = pointBounds51993 := by
 decide +kernel
def cuts51994 : List PrefixCut := [⟨58,211468944,211469062⟩,
⟨64,234089258,234089389⟩]
theorem checked51994 : checkPrefixCuts (2^48) 6818889729 10 Manual.Count131072.C051994.packed 64 cuts51994 = true := by
 decide +kernel
def pointBounds51994 : List (Nat × Nat × Nat) := [(6819008512,112143335533245,112143722931890)]
theorem point_links_checked51994 : (cuts51994.take 1).map (fun c => (6818889729-1+2*2^10*c.k,112143124064301+c.lower,112143511462828+c.upper)) = pointBounds51994 := by
 decide +kernel
def cuts51995 : List PrefixCut := [⟨64,240152562,240152701⟩]
theorem checked51995 : checkPrefixCuts (2^48) 6819020801 10 Manual.Count131072.C051995.packed 64 cuts51995 = true := by
 decide +kernel
def cuts51996 : List PrefixCut := [⟨35,131466909,131466985⟩,
⟨64,240890903,240891043⟩]
theorem checked51996 : checkPrefixCuts (2^48) 6819151873 10 Manual.Count131072.C051996.packed 64 cuts51996 = true := by
 decide +kernel
def pointBounds51996 : List (Nat × Nat × Nat) := [(6819223552,112143729773030,112144117171903)]
theorem point_links_checked51996 : (cuts51996.take 1).map (fun c => (6819151873-1+2*2^10*c.k,112143598306121+c.lower,112143985704918+c.upper)) = pointBounds51996 := by
 decide +kernel
def cuts51997 : List PrefixCut := [⟨64,239771829,239771968⟩]
theorem checked51997 : checkPrefixCuts (2^48) 6819282945 10 Manual.Count131072.C051997.packed 64 cuts51997 = true := by
 decide +kernel
def cuts51998 : List PrefixCut := [⟨12,45526822,45526849⟩,
⟨64,240303810,240303948⟩]
theorem checked51998 : checkPrefixCuts (2^48) 6819414017 10 Manual.Count131072.C051998.packed 64 cuts51998 = true := by
 decide +kernel
def pointBounds51998 : List (Nat × Nat × Nat) := [(6819438592,112144124495675,112144511894778)]
theorem point_links_checked51998 : (cuts51998.take 1).map (fun c => (6819414017-1+2*2^10*c.k,112144078968853+c.lower,112144466367929+c.upper)) = pointBounds51998 := by
 decide +kernel
def cuts51999 : List PrefixCut := [⟨53,197704412,197704522⟩,
⟨64,238730777,238730910⟩]
theorem checked51999 : checkPrefixCuts (2^48) 6819545089 10 Manual.Count131072.C051999.packed 64 cuts51999 = true := by
 decide +kernel
def pointBounds51999 : List (Nat × Nat × Nat) := [(6819653632,112144516977075,112144904376399)]
theorem point_links_checked51999 : (cuts51999.take 1).map (fun c => (6819545089-1+2*2^10*c.k,112144319272663+c.lower,112144706671877+c.upper)) = pointBounds51999 := by
 decide +kernel
def cuts52000 : List PrefixCut := [⟨64,241450206,241450348⟩]
theorem checked52000 : checkPrefixCuts (2^48) 6819676161 10 Manual.Count131072.C052000.packed 64 cuts52000 = true := by
 decide +kernel
def cuts52001 : List PrefixCut := [⟨30,111478264,111478323⟩,
⟨64,238061213,238061347⟩]
theorem checked52001 : checkPrefixCuts (2^48) 6819807233 10 Manual.Count131072.C052001.packed 64 cuts52001 = true := by
 decide +kernel
def pointBounds52001 : List (Nat × Nat × Nat) := [(6819868672,112144910931910,112145298331458)]
theorem point_links_checked52001 : (cuts52001.take 1).map (fun c => (6819807233-1+2*2^10*c.k,112144799453646+c.lower,112145186853135+c.upper)) = pointBounds52001 := by
 decide +kernel
def cuts52002 : List PrefixCut := [⟨64,236942316,236942449⟩]
theorem checked52002 : checkPrefixCuts (2^48) 6819938305 10 Manual.Count131072.C052002.packed 64 cuts52002 = true := by
 decide +kernel
def cuts52003 : List PrefixCut := [⟨7,26289955,26289970⟩,
⟨64,240652150,240652290⟩]
theorem checked52003 : checkPrefixCuts (2^48) 6820069377 10 Manual.Count131072.C052003.packed 64 cuts52003 = true := by
 decide +kernel
def pointBounds52003 : List (Nat × Nat × Nat) := [(6820083712,112145300747130,112145688146901)]
theorem point_links_checked52003 : (cuts52003.take 1).map (fun c => (6820069377-1+2*2^10*c.k,112145274457175+c.lower,112145661856931+c.upper)) = pointBounds52003 := by
 decide +kernel
def cuts52004 : List PrefixCut := [⟨48,178577314,178577417⟩,
⟨64,238749078,238749215⟩]
theorem checked52004 : checkPrefixCuts (2^48) 6820200449 10 Manual.Count131072.C052004.packed 64 cuts52004 = true := by
 decide +kernel
def pointBounds52004 : List (Nat × Nat × Nat) := [(6820298752,112145693686639,112146081086638)]
theorem point_links_checked52004 : (cuts52004.take 1).map (fun c => (6820200449-1+2*2^10*c.k,112145515109325+c.lower,112145902509221+c.upper)) = pointBounds52004 := by
 decide +kernel
def cuts52005 : List PrefixCut := [⟨64,238084196,238084333⟩]
theorem checked52005 : checkPrefixCuts (2^48) 6820331521 10 Manual.Count131072.C052005.packed 64 cuts52005 = true := by
 decide +kernel
def cuts52006 : List PrefixCut := [⟨25,93969572,93969628⟩,
⟨64,239482747,239482886⟩]
theorem checked52006 : checkPrefixCuts (2^48) 6820462593 10 Manual.Count131072.C052006.packed 64 cuts52006 = true := by
 decide +kernel
def pointBounds52006 : List (Nat × Nat × Nat) := [(6820513792,112146085912171,112146473312397)]
theorem point_links_checked52006 : (cuts52006.take 1).map (fun c => (6820462593-1+2*2^10*c.k,112145991942599+c.lower,112146379342769+c.upper)) = pointBounds52006 := by
 decide +kernel
def cuts52007 : List PrefixCut := [⟨64,241046329,241046473⟩]
theorem checked52007 : checkPrefixCuts (2^48) 6820593665 10 Manual.Count131072.C052007.packed 64 cuts52007 = true := by
 decide +kernel
def cuts52008 : List PrefixCut := [⟨2,6561545,6561549⟩,
⟨64,239349729,239349863⟩]
theorem checked52008 : checkPrefixCuts (2^48) 6820724737 10 Manual.Count131072.C052008.packed 64 cuts52008 = true := by
 decide +kernel
def pointBounds52008 : List (Nat × Nat × Nat) := [(6820728832,112146479033220,112146866433677)]
theorem point_links_checked52008 : (cuts52008.take 1).map (fun c => (6820724737-1+2*2^10*c.k,112146472471675+c.lower,112146859872128+c.upper)) = pointBounds52008 := by
 decide +kernel
def cuts52009 : List PrefixCut := [⟨43,159660210,159660301⟩,
⟨64,237240554,237240689⟩]
theorem checked52009 : checkPrefixCuts (2^48) 6820855809 10 Manual.Count131072.C052009.packed 64 cuts52009 = true := by
 decide +kernel
def pointBounds52009 : List (Nat × Nat × Nat) := [(6820943872,112146871481614,112147258882292)]
theorem point_links_checked52009 : (cuts52009.take 1).map (fun c => (6820855809-1+2*2^10*c.k,112146711821404+c.lower,112147099221991+c.upper)) = pointBounds52009 := by
 decide +kernel
def cuts52010 : List PrefixCut := [⟨64,240165859,240165997⟩]
theorem checked52010 : checkPrefixCuts (2^48) 6820986881 10 Manual.Count131072.C052010.packed 64 cuts52010 = true := by
 decide +kernel
def cuts52011 : List PrefixCut := [⟨20,75184990,75185035⟩,
⟨64,240986537,240986676⟩]
theorem checked52011 : checkPrefixCuts (2^48) 6821117953 10 Manual.Count131072.C052011.packed 64 cuts52011 = true := by
 decide +kernel
def pointBounds52011 : List (Nat × Nat × Nat) := [(6821158912,112147264412807,112147651813712)]
theorem point_links_checked52011 : (cuts52011.take 1).map (fun c => (6821117953-1+2*2^10*c.k,112147189227817+c.lower,112147576628677+c.upper)) = pointBounds52011 := by
 decide +kernel
def cuts52012 : List PrefixCut := [⟨61,227860033,227860166⟩,
⟨64,238052153,238052292⟩]
theorem checked52012 : checkPrefixCuts (2^48) 6821249025 10 Manual.Count131072.C052012.packed 64 cuts52012 = true := by
 decide +kernel
def pointBounds52012 : List (Nat × Nat × Nat) := [(6821373952,112147658074387,112148045475519)]
theorem point_links_checked52012 : (cuts52012.take 1).map (fun c => (6821249025-1+2*2^10*c.k,112147430214354+c.lower,112147817615353+c.upper)) = pointBounds52012 := by
 decide +kernel
def cuts52013 : List PrefixCut := [⟨64,239037905,239038036⟩]
theorem checked52013 : checkPrefixCuts (2^48) 6821380097 10 Manual.Count131072.C052013.packed 64 cuts52013 = true := by
 decide +kernel
def cuts52014 : List PrefixCut := [⟨38,141860829,141860914⟩,
⟨64,239858562,239858703⟩]
theorem checked52014 : checkPrefixCuts (2^48) 6821511169 10 Manual.Count131072.C052014.packed 64 cuts52014 = true := by
 decide +kernel
def pointBounds52014 : List (Nat × Nat × Nat) := [(6821588992,112148049165241,112148436566595)]
theorem point_links_checked52014 : (cuts52014.take 1).map (fun c => (6821511169-1+2*2^10*c.k,112147907304412+c.lower,112148294705681+c.upper)) = pointBounds52014 := by
 decide +kernel
def cuts52015 : List PrefixCut := [⟨64,237997161,237997296⟩]
theorem checked52015 : checkPrefixCuts (2^48) 6821642241 10 Manual.Count131072.C052015.packed 64 cuts52015 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000062
