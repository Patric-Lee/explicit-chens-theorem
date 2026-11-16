import PlattAssemblyKernel
import PlattCertificates.Count131072.C040992
import PlattCertificates.Count131072.C040993
import PlattCertificates.Count131072.C040994
import PlattCertificates.Count131072.C040995
import PlattCertificates.Count131072.C040996
import PlattCertificates.Count131072.C040997
import PlattCertificates.Count131072.C040998
import PlattCertificates.Count131072.C040999
import PlattCertificates.Count131072.C041000
import PlattCertificates.Count131072.C041001
import PlattCertificates.Count131072.C041002
import PlattCertificates.Count131072.C041003
import PlattCertificates.Count131072.C041004
import PlattCertificates.Count131072.C041005
import PlattCertificates.Count131072.C041006
import PlattCertificates.Count131072.C041007
import PlattCertificates.Count131072.C041008
import PlattCertificates.Count131072.C041009
import PlattCertificates.Count131072.C041010
import PlattCertificates.Count131072.C041011
import PlattCertificates.Count131072.C041012
import PlattCertificates.Count131072.C041013
import PlattCertificates.Count131072.C041014
import PlattCertificates.Count131072.C041015
import PlattCertificates.Count131072.C041016
import PlattCertificates.Count131072.C041017
import PlattCertificates.Count131072.C041018
import PlattCertificates.Count131072.C041019
import PlattCertificates.Count131072.C041020
import PlattCertificates.Count131072.C041021
import PlattCertificates.Count131072.C041022
import PlattCertificates.Count131072.C041023
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000031
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40992 : List PrefixCut := [⟨62,294881524,294881700⟩,
⟨64,304147171,304147353⟩]
theorem checked40992 : checkPrefixCuts (2^48) 5376835585 10 Manual.Count131072.C040992.packed 64 cuts40992 = true := by
 decide +kernel
def pointBounds40992 : List (Nat × Nat × Nat) := [(5376962560,109174210132145,109174595820148)]
theorem point_links_checked40992 : (cuts40992.take 1).map (fun c => (5376835585-1+2*2^10*c.k,109173915250621+c.lower,109174300938448+c.upper)) = pointBounds40992 := by
 decide +kernel
def cuts40993 : List PrefixCut := [⟨64,311468420,311468606⟩]
theorem checked40993 : checkPrefixCuts (2^48) 5376966657 10 Manual.Count131072.C040993.packed 64 cuts40993 = true := by
 decide +kernel
def cuts40994 : List PrefixCut := [⟨17,79200740,79200788⟩,
⟨64,304236982,304237161⟩]
theorem checked40994 : checkPrefixCuts (2^48) 5377097729 10 Manual.Count131072.C040994.packed 64 cuts40994 = true := by
 decide +kernel
def pointBounds40994 : List (Nat × Nat × Nat) := [(5377132544,109174610066952,109174995755195)]
theorem point_links_checked40994 : (cuts40994.take 1).map (fun c => (5377097729-1+2*2^10*c.k,109174530866212+c.lower,109174916554407+c.upper)) = pointBounds40994 := by
 decide +kernel
def cuts40995 : List PrefixCut := [⟨36,169808335,169808432⟩,
⟨64,305276467,305276646⟩]
theorem checked40995 : checkPrefixCuts (2^48) 5377228801 10 Manual.Count131072.C040995.packed 64 cuts40995 = true := by
 decide +kernel
def pointBounds40995 : List (Nat × Nat × Nat) := [(5377302528,109175004911529,109175390600000)]
theorem point_links_checked40995 : (cuts40995.take 1).map (fun c => (5377228801-1+2*2^10*c.k,109174835103194+c.lower,109175220791568+c.upper)) = pointBounds40995 := by
 decide +kernel
def cuts40996 : List PrefixCut := [⟨55,265488207,265488364⟩,
⟨64,309247168,309247352⟩]
theorem checked40996 : checkPrefixCuts (2^48) 5377359873 10 Manual.Count131072.C040996.packed 64 cuts40996 = true := by
 decide +kernel
def pointBounds40996 : List (Nat × Nat × Nat) := [(5377472512,109175405867868,109175791556578)]
theorem point_links_checked40996 : (cuts40996.take 1).map (fun c => (5377359873-1+2*2^10*c.k,109175140379661+c.lower,109175526068214+c.upper)) = pointBounds40996 := by
 decide +kernel
def cuts40997 : List PrefixCut := [⟨64,306622546,306622721⟩]
theorem checked40997 : checkPrefixCuts (2^48) 5377490945 10 Manual.Count131072.C040997.packed 64 cuts40997 = true := by
 decide +kernel
def cuts40998 : List PrefixCut := [⟨10,46165456,46165483⟩,
⟨64,305358825,305359006⟩]
theorem checked40998 : checkPrefixCuts (2^48) 5377622017 10 Manual.Count131072.C040998.packed 64 cuts40998 = true := by
 decide +kernel
def pointBounds40998 : List (Nat × Nat × Nat) := [(5377642496,109175802414831,109176188103770)]
theorem point_links_checked40998 : (cuts40998.take 1).map (fun c => (5377622017-1+2*2^10*c.k,109175756249375+c.lower,109176141938287+c.upper)) = pointBounds40998 := by
 decide +kernel
def cuts40999 : List PrefixCut := [⟨29,137445695,137445774⟩,
⟨64,308701153,308701335⟩]
theorem checked40999 : checkPrefixCuts (2^48) 5377753089 10 Manual.Count131072.C040999.packed 64 cuts40999 = true := by
 decide +kernel
def pointBounds40999 : List (Nat × Nat × Nat) := [(5377812480,109176199053895,109176584743067)]
theorem point_links_checked40999 : (cuts40999.take 1).map (fun c => (5377753089-1+2*2^10*c.k,109176061608200+c.lower,109176447297293+c.upper)) = pointBounds40999 := by
 decide +kernel
def cuts41000 : List PrefixCut := [⟨48,228982535,228982666⟩,
⟨64,306390768,306390944⟩]
theorem checked41000 : checkPrefixCuts (2^48) 5377884161 10 Manual.Count131072.C041000.packed 64 cuts41000 = true := by
 decide +kernel
def pointBounds41000 : List (Nat × Nat × Nat) := [(5377982464,109176599291888,109176984981294)]
theorem point_links_checked41000 : (cuts41000.take 1).map (fun c => (5377884161-1+2*2^10*c.k,109176370309353+c.lower,109176755998628+c.upper)) = pointBounds41000 := by
 decide +kernel
def cuts41001 : List PrefixCut := [⟨64,303033682,303033861⟩]
theorem checked41001 : checkPrefixCuts (2^48) 5378015233 10 Manual.Count131072.C041001.packed 64 cuts41001 = true := by
 decide +kernel
def cuts41002 : List PrefixCut := [⟨3,14130923,14130932⟩,
⟨64,305381446,305381625⟩]
theorem checked41002 : checkPrefixCuts (2^48) 5378146305 10 Manual.Count131072.C041002.packed 64 cuts41002 = true := by
 decide +kernel
def pointBounds41002 : List (Nat × Nat × Nat) := [(5378152448,109176993864726,109177379554365)]
theorem point_links_checked41002 : (cuts41002.take 1).map (fun c => (5378146305-1+2*2^10*c.k,109176979733803+c.lower,109177365423433+c.upper)) = pointBounds41002 := by
 decide +kernel
def cuts41003 : List PrefixCut := [⟨22,108020046,108020106⟩,
⟨64,311130832,311131012⟩]
theorem checked41003 : checkPrefixCuts (2^48) 5378277377 10 Manual.Count131072.C041003.packed 64 cuts41003 = true := by
 decide +kernel
def pointBounds41003 : List (Nat × Nat × Nat) := [(5378322432,109177393135295,109177778825164)]
theorem point_links_checked41003 : (cuts41003.take 1).map (fun c => (5378277377-1+2*2^10*c.k,109177285115249+c.lower,109177670805058+c.upper)) = pointBounds41003 := by
 decide +kernel
def cuts41004 : List PrefixCut := [⟨41,196094854,196094969⟩,
⟨64,306884215,306884392⟩]
theorem checked41004 : checkPrefixCuts (2^48) 5378408449 10 Manual.Count131072.C041004.packed 64 cuts41004 = true := by
 decide +kernel
def pointBounds41004 : List (Nat × Nat × Nat) := [(5378492416,109177792340935,109178178031039)]
theorem point_links_checked41004 : (cuts41004.take 1).map (fun c => (5378408449-1+2*2^10*c.k,109177596246081+c.lower,109177981936070+c.upper)) = pointBounds41004 := by
 decide +kernel
def cuts41005 : List PrefixCut := [⟨60,285002086,285002254⟩,
⟨64,304521819,304521998⟩]
theorem checked41005 : checkPrefixCuts (2^48) 5378539521 10 Manual.Count131072.C041005.packed 64 cuts41005 = true := by
 decide +kernel
def pointBounds41005 : List (Nat × Nat × Nat) := [(5378662400,109178188132382,109178573822716)]
theorem point_links_checked41005 : (cuts41005.take 1).map (fun c => (5378539521-1+2*2^10*c.k,109177903130296+c.lower,109178288820462+c.upper)) = pointBounds41005 := by
 decide +kernel
def cuts41006 : List PrefixCut := [⟨64,304619034,304619214⟩]
theorem checked41006 : checkPrefixCuts (2^48) 5378670593 10 Manual.Count131072.C041006.packed 64 cuts41006 = true := by
 decide +kernel
def cuts41007 : List PrefixCut := [⟨15,73994986,73995028⟩,
⟨64,308641041,308641222⟩]
theorem checked41007 : checkPrefixCuts (2^48) 5378801665 10 Manual.Count131072.C041007.packed 64 cuts41007 = true := by
 decide +kernel
def pointBounds41007 : List (Nat × Nat × Nat) := [(5378832384,109178586266135,109178971956702)]
theorem point_links_checked41007 : (cuts41007.take 1).map (fun c => (5378801665-1+2*2^10*c.k,109178512271149+c.lower,109178897961674+c.upper)) = pointBounds41007 := by
 decide +kernel
def cuts41008 : List PrefixCut := [⟨34,160440086,160440180⟩,
⟨64,304813468,304813651⟩]
theorem checked41008 : checkPrefixCuts (2^48) 5378932737 10 Manual.Count131072.C041008.packed 64 cuts41008 = true := by
 decide +kernel
def pointBounds41008 : List (Nat × Nat × Nat) := [(5379002368,109178981352276,109179367043076)]
theorem point_links_checked41008 : (cuts41008.take 1).map (fun c => (5378932737-1+2*2^10*c.k,109178820912190+c.lower,109179206602896+c.upper)) = pointBounds41008 := by
 decide +kernel
def cuts41009 : List PrefixCut := [⟨53,253787551,253787703⟩,
⟨64,303602564,303602744⟩]
theorem checked41009 : checkPrefixCuts (2^48) 5379063809 10 Manual.Count131072.C041009.packed 64 cuts41009 = true := by
 decide +kernel
def pointBounds41009 : List (Nat × Nat × Nat) := [(5379172352,109179379513209,109179765204250)]
theorem point_links_checked41009 : (cuts41009.take 1).map (fun c => (5379063809-1+2*2^10*c.k,109179125725658+c.lower,109179511416547+c.upper)) = pointBounds41009 := by
 decide +kernel
def cuts41010 : List PrefixCut := [⟨64,307571910,307572093⟩]
theorem checked41010 : checkPrefixCuts (2^48) 5379194881 10 Manual.Count131072.C041010.packed 64 cuts41010 = true := by
 decide +kernel
def cuts41011 : List PrefixCut := [⟨8,39191598,39191620⟩,
⟨64,307145791,307145973⟩]
theorem checked41011 : checkPrefixCuts (2^48) 5379325953 10 Manual.Count131072.C041011.packed 64 cuts41011 = true := by
 decide +kernel
def pointBounds41011 : List (Nat × Nat × Nat) := [(5379342336,109179776091730,109180161783004)]
theorem point_links_checked41011 : (cuts41011.take 1).map (fun c => (5379325953-1+2*2^10*c.k,109179736900132+c.lower,109180122591384+c.upper)) = pointBounds41011 := by
 decide +kernel
def cuts41012 : List PrefixCut := [⟨27,129815262,129815339⟩,
⟨64,308655718,308655901⟩]
theorem checked41012 : checkPrefixCuts (2^48) 5379457025 10 Manual.Count131072.C041012.packed 64 cuts41012 = true := by
 decide +kernel
def pointBounds41012 : List (Nat × Nat × Nat) := [(5379512320,109180173861185,109180559552696)]
theorem point_links_checked41012 : (cuts41012.take 1).map (fun c => (5379457025-1+2*2^10*c.k,109180044045923+c.lower,109180429737357+c.upper)) = pointBounds41012 := by
 decide +kernel
def cuts41013 : List PrefixCut := [⟨46,217713095,217713222⟩,
⟨64,305508847,305509024⟩]
theorem checked41013 : checkPrefixCuts (2^48) 5379588097 10 Manual.Count131072.C041013.packed 64 cuts41013 = true := by
 decide +kernel
def pointBounds41013 : List (Nat × Nat × Nat) := [(5379682304,109180570414736,109180956106480)]
theorem point_links_checked41013 : (cuts41013.take 1).map (fun c => (5379588097-1+2*2^10*c.k,109180352701641+c.lower,109180738393258+c.upper)) = pointBounds41013 := by
 decide +kernel
def cuts41014 : List PrefixCut := [⟨64,303460867,303461049⟩]
theorem checked41014 : checkPrefixCuts (2^48) 5379719169 10 Manual.Count131072.C041014.packed 64 cuts41014 = true := by
 decide +kernel
def cuts41015 : List PrefixCut := [⟨1,4761138,4761141⟩,
⟨64,307534490,307534673⟩]
theorem checked41015 : checkPrefixCuts (2^48) 5379850241 10 Manual.Count131072.C041015.packed 64 cuts41015 = true := by
 decide +kernel
def pointBounds41015 : List (Nat × Nat × Nat) := [(5379852288,109180966432493,109181352124472)]
theorem point_links_checked41015 : (cuts41015.take 1).map (fun c => (5379850241-1+2*2^10*c.k,109180961671355+c.lower,109181347363331+c.upper)) = pointBounds41015 := by
 decide +kernel
def cuts41016 : List PrefixCut := [⟨20,94696914,94696970⟩,
⟨64,306689848,306690029⟩]
theorem checked41016 : checkPrefixCuts (2^48) 5379981313 10 Manual.Count131072.C041016.packed 64 cuts41016 = true := by
 decide +kernel
def pointBounds41016 : List (Nat × Nat × Nat) := [(5380022272,109181363902759,109181749594974)]
theorem point_links_checked41016 : (cuts41016.take 1).map (fun c => (5379981313-1+2*2^10*c.k,109181269205845+c.lower,109181654898004+c.upper)) = pointBounds41016 := by
 decide +kernel
def cuts41017 : List PrefixCut := [⟨39,185046182,185046290⟩,
⟨64,307467106,307467288⟩]
theorem checked41017 : checkPrefixCuts (2^48) 5380112385 10 Manual.Count131072.C041017.packed 64 cuts41017 = true := by
 decide +kernel
def pointBounds41017 : List (Nat × Nat × Nat) := [(5380192256,109181760941875,109182146634323)]
theorem point_links_checked41017 : (cuts41017.take 1).map (fun c => (5380112385-1+2*2^10*c.k,109181575895693+c.lower,109181961588033+c.upper)) = pointBounds41017 := by
 decide +kernel
def cuts41018 : List PrefixCut := [⟨58,281877585,281877753⟩,
⟨64,310598613,310598798⟩]
theorem checked41018 : checkPrefixCuts (2^48) 5380243457 10 Manual.Count131072.C041018.packed 64 cuts41018 = true := by
 decide +kernel
def pointBounds41018 : List (Nat × Nat × Nat) := [(5380362240,109182165240384,109182550933074)]
theorem point_links_checked41018 : (cuts41018.take 1).map (fun c => (5380243457-1+2*2^10*c.k,109181883362799+c.lower,109182269055321+c.upper)) = pointBounds41018 := by
 decide +kernel
def cuts41019 : List PrefixCut := [⟨64,305673462,305673639⟩]
theorem checked41019 : checkPrefixCuts (2^48) 5380374529 10 Manual.Count131072.C041019.packed 64 cuts41019 = true := by
 decide +kernel
def cuts41020 : List PrefixCut := [⟨13,64555113,64555152⟩,
⟨64,307444701,307444885⟩]
theorem checked41020 : checkPrefixCuts (2^48) 5380505601 10 Manual.Count131072.C041020.packed 64 cuts41020 = true := by
 decide +kernel
def pointBounds41020 : List (Nat × Nat × Nat) := [(5380532224,109182564189987,109182949882910)]
theorem point_links_checked41020 : (cuts41020.take 1).map (fun c => (5380505601-1+2*2^10*c.k,109182499634874+c.lower,109182885327758+c.upper)) = pointBounds41020 := by
 decide +kernel
def cuts41021 : List PrefixCut := [⟨32,152071705,152071794⟩,
⟨64,305553966,305554142⟩]
theorem checked41021 : checkPrefixCuts (2^48) 5380636673 10 Manual.Count131072.C041021.packed 64 cuts41021 = true := by
 decide +kernel
def pointBounds41021 : List (Nat × Nat × Nat) := [(5380702208,109182959151280,109183344844437)]
theorem point_links_checked41021 : (cuts41021.take 1).map (fun c => (5380636673-1+2*2^10*c.k,109182807079575+c.lower,109183192772643+c.upper)) = pointBounds41021 := by
 decide +kernel
def cuts41022 : List PrefixCut := [⟨51,242303543,242303682⟩,
⟨64,305075714,305075891⟩]
theorem checked41022 : checkPrefixCuts (2^48) 5380767745 10 Manual.Count131072.C041022.packed 64 cuts41022 = true := by
 decide +kernel
def pointBounds41022 : List (Nat × Nat × Nat) := [(5380872192,109183354937084,109183740630467)]
theorem point_links_checked41022 : (cuts41022.take 1).map (fun c => (5380767745-1+2*2^10*c.k,109183112633541+c.lower,109183498326785+c.upper)) = pointBounds41022 := by
 decide +kernel
def cuts41023 : List PrefixCut := [⟨64,304545193,304545372⟩]
theorem checked41023 : checkPrefixCuts (2^48) 5380898817 10 Manual.Count131072.C041023.packed 64 cuts41023 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000031
