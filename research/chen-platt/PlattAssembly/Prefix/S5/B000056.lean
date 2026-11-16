import PlattAssemblyKernel
import PlattCertificates.Count131072.C041792
import PlattCertificates.Count131072.C041793
import PlattCertificates.Count131072.C041794
import PlattCertificates.Count131072.C041795
import PlattCertificates.Count131072.C041796
import PlattCertificates.Count131072.C041797
import PlattCertificates.Count131072.C041798
import PlattCertificates.Count131072.C041799
import PlattCertificates.Count131072.C041800
import PlattCertificates.Count131072.C041801
import PlattCertificates.Count131072.C041802
import PlattCertificates.Count131072.C041803
import PlattCertificates.Count131072.C041804
import PlattCertificates.Count131072.C041805
import PlattCertificates.Count131072.C041806
import PlattCertificates.Count131072.C041807
import PlattCertificates.Count131072.C041808
import PlattCertificates.Count131072.C041809
import PlattCertificates.Count131072.C041810
import PlattCertificates.Count131072.C041811
import PlattCertificates.Count131072.C041812
import PlattCertificates.Count131072.C041813
import PlattCertificates.Count131072.C041814
import PlattCertificates.Count131072.C041815
import PlattCertificates.Count131072.C041816
import PlattCertificates.Count131072.C041817
import PlattCertificates.Count131072.C041818
import PlattCertificates.Count131072.C041819
import PlattCertificates.Count131072.C041820
import PlattCertificates.Count131072.C041821
import PlattCertificates.Count131072.C041822
import PlattCertificates.Count131072.C041823
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000056
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts41792 : List PrefixCut := [⟨64,301050716,301050888⟩]
theorem checked41792 : checkPrefixCuts (2^48) 5481693185 10 Manual.Count131072.C041792.packed 64 cuts41792 = true := by
 decide +kernel
def cuts41793 : List PrefixCut := [⟨5,23054754,23054768⟩,
⟨64,301865024,301865201⟩]
theorem checked41793 : checkPrefixCuts (2^48) 5481824257 10 Manual.Count131072.C041793.packed 64 cuts41793 = true := by
 decide +kernel
def pointBounds41793 : List (Nat × Nat × Nat) := [(5481834496,109416757421781,109417143252558)]
theorem point_links_checked41793 : (cuts41793.take 1).map (fun c => (5481824257-1+2*2^10*c.k,109416734367027+c.lower,109417120197790+c.upper)) = pointBounds41793 := by
 decide +kernel
def cuts41794 : List PrefixCut := [⟨25,116810946,116811015⟩,
⟨64,295850473,295850642⟩]
theorem checked41794 : checkPrefixCuts (2^48) 5481955329 10 Manual.Count131072.C041794.packed 64 cuts41794 = true := by
 decide +kernel
def pointBounds41794 : List (Nat × Nat × Nat) := [(5482006528,109417153042997,109417538874006)]
theorem point_links_checked41794 : (cuts41794.take 1).map (fun c => (5481955329-1+2*2^10*c.k,109417036232051+c.lower,109417422062991+c.upper)) = pointBounds41794 := by
 decide +kernel
def cuts41795 : List PrefixCut := [⟨45,215645013,215645143⟩,
⟨64,302312742,302312922⟩]
theorem checked41795 : checkPrefixCuts (2^48) 5482086401 10 Manual.Count131072.C041795.packed 64 cuts41795 = true := by
 decide +kernel
def pointBounds41795 : List (Nat × Nat × Nat) := [(5482178560,109417547727537,109417933558776)]
theorem point_links_checked41795 : (cuts41795.take 1).map (fun c => (5482086401-1+2*2^10*c.k,109417332082524+c.lower,109417717913633+c.upper)) = pointBounds41795 := by
 decide +kernel
def cuts41796 : List PrefixCut := [⟨64,301894759,301894941⟩]
theorem checked41796 : checkPrefixCuts (2^48) 5482217473 10 Manual.Count131072.C041796.packed 64 cuts41796 = true := by
 decide +kernel
def cuts41797 : List PrefixCut := [⟨1,4518098,4518100⟩,
⟨64,303222393,303222565⟩]
theorem checked41797 : checkPrefixCuts (2^48) 5482348545 10 Manual.Count131072.C041797.packed 64 cuts41797 = true := by
 decide +kernel
def pointBounds41797 : List (Nat × Nat × Nat) := [(5482350592,109417940808123,109418326639596)]
theorem point_links_checked41797 : (cuts41797.take 1).map (fun c => (5482348545-1+2*2^10*c.k,109417936290025+c.lower,109418322121496+c.upper)) = pointBounds41797 := by
 decide +kernel
def cuts41798 : List PrefixCut := [⟨21,97906521,97906582⟩,
⟨64,298902546,298902726⟩]
theorem checked41798 : checkPrefixCuts (2^48) 5482479617 10 Manual.Count131072.C041798.packed 64 cuts41798 = true := by
 decide +kernel
def pointBounds41798 : List (Nat × Nat × Nat) := [(5482522624,109418337418939,109418723250643)]
theorem point_links_checked41798 : (cuts41798.take 1).map (fun c => (5482479617-1+2*2^10*c.k,109418239512418+c.lower,109418625344061+c.upper)) = pointBounds41798 := by
 decide +kernel
def cuts41799 : List PrefixCut := [⟨41,191289774,191289890⟩,
⟨64,299203447,299203626⟩]
theorem checked41799 : checkPrefixCuts (2^48) 5482610689 10 Manual.Count131072.C041799.packed 64 cuts41799 = true := by
 decide +kernel
def pointBounds41799 : List (Nat × Nat × Nat) := [(5482694656,109418729704738,109419115536677)]
theorem point_links_checked41799 : (cuts41799.take 1).map (fun c => (5482610689-1+2*2^10*c.k,109418538414964+c.lower,109418924246787+c.upper)) = pointBounds41799 := by
 decide +kernel
def cuts41800 : List PrefixCut := [⟨61,279585442,279585606⟩,
⟨64,294473215,294473388⟩]
theorem checked41800 : checkPrefixCuts (2^48) 5482741761 10 Manual.Count131072.C041800.packed 64 cuts41800 = true := by
 decide +kernel
def pointBounds41800 : List (Nat × Nat × Nat) := [(5482866688,109419117203853,109419503036019)]
theorem point_links_checked41800 : (cuts41800.take 1).map (fun c => (5482741761-1+2*2^10*c.k,109418837618411+c.lower,109419223450413+c.upper)) = pointBounds41800 := by
 decide +kernel
def cuts41801 : List PrefixCut := [⟨64,296673665,296673838⟩]
theorem checked41801 : checkPrefixCuts (2^48) 5482872833 10 Manual.Count131072.C041801.packed 64 cuts41801 = true := by
 decide +kernel
def cuts41802 : List PrefixCut := [⟨17,79519045,79519094⟩,
⟨64,302416123,302416301⟩]
theorem checked41802 : checkPrefixCuts (2^48) 5483003905 10 Manual.Count131072.C041802.packed 64 cuts41802 = true := by
 decide +kernel
def pointBounds41802 : List (Nat × Nat × Nat) := [(5483038720,109419508284336,109419894116733)]
theorem point_links_checked41802 : (cuts41802.take 1).map (fun c => (5483003905-1+2*2^10*c.k,109419428765291+c.lower,109419814597639+c.upper)) = pointBounds41802 := by
 decide +kernel
def cuts41803 : List PrefixCut := [⟨37,171456594,171456700⟩,
⟨64,298456155,298456335⟩]
theorem checked41803 : checkPrefixCuts (2^48) 5483134977 10 Manual.Count131072.C041803.packed 64 cuts41803 = true := by
 decide +kernel
def pointBounds41803 : List (Nat × Nat × Nat) := [(5483210752,109419902638008,109420288470640)]
theorem point_links_checked41803 : (cuts41803.take 1).map (fun c => (5483134977-1+2*2^10*c.k,109419731181414+c.lower,109420117013940+c.upper)) = pointBounds41803 := by
 decide +kernel
def cuts41804 : List PrefixCut := [⟨57,269189677,269189831⟩,
⟨64,301529012,301529186⟩]
theorem checked41804 : checkPrefixCuts (2^48) 5483266049 10 Manual.Count131072.C041804.packed 64 cuts41804 = true := by
 decide +kernel
def pointBounds41804 : List (Nat × Nat × Nat) := [(5483382784,109420298827246,109420684660106)]
theorem point_links_checked41804 : (cuts41804.take 1).map (fun c => (5483266049-1+2*2^10*c.k,109420029637569+c.lower,109420415470275+c.upper)) = pointBounds41804 := by
 decide +kernel
def cuts41805 : List PrefixCut := [⟨64,300546507,300546686⟩]
theorem checked41805 : checkPrefixCuts (2^48) 5483397121 10 Manual.Count131072.C041805.packed 64 cuts41805 = true := by
 decide +kernel
def cuts41806 : List PrefixCut := [⟨13,58979155,58979189⟩,
⟨64,297664801,297664978⟩]
theorem checked41806 : checkPrefixCuts (2^48) 5483528193 10 Manual.Count131072.C041806.packed 64 cuts41806 = true := by
 decide +kernel
def pointBounds41806 : List (Nat × Nat × Nat) := [(5483554816,109420690692243,109421076525336)]
theorem point_links_checked41806 : (cuts41806.take 1).map (fun c => (5483528193-1+2*2^10*c.k,109420631713088+c.lower,109421017546147+c.upper)) = pointBounds41806 := by
 decide +kernel
def cuts41807 : List PrefixCut := [⟨33,154706937,154707027⟩,
⟨64,296169170,296169346⟩]
theorem checked41807 : checkPrefixCuts (2^48) 5483659265 10 Manual.Count131072.C041807.packed 64 cuts41807 = true := by
 decide +kernel
def pointBounds41807 : List (Nat × Nat × Nat) := [(5483726848,109421084084826,109421469918152)]
theorem point_links_checked41807 : (cuts41807.take 1).map (fun c => (5483659265-1+2*2^10*c.k,109420929377889+c.lower,109421315211125+c.upper)) = pointBounds41807 := by
 decide +kernel
def cuts41808 : List PrefixCut := [⟨53,250070117,250070262⟩,
⟨64,300884250,300884427⟩]
theorem checked41808 : checkPrefixCuts (2^48) 5483790337 10 Manual.Count131072.C041808.packed 64 cuts41808 = true := by
 decide +kernel
def pointBounds41808 : List (Nat × Nat × Nat) := [(5483898880,109421475617176,109421861450733)]
theorem point_links_checked41808 : (cuts41808.take 1).map (fun c => (5483790337-1+2*2^10*c.k,109421225547059+c.lower,109421611380471+c.upper)) = pointBounds41808 := by
 decide +kernel
def cuts41809 : List PrefixCut := [⟨64,299388596,299388775⟩]
theorem checked41809 : checkPrefixCuts (2^48) 5483921409 10 Manual.Count131072.C041809.packed 64 cuts41809 = true := by
 decide +kernel
def cuts41810 : List PrefixCut := [⟨9,42241290,42241313⟩,
⟨64,301947709,301947887⟩]
theorem checked41810 : checkPrefixCuts (2^48) 5484052481 10 Manual.Count131072.C041810.packed 64 cuts41810 = true := by
 decide +kernel
def pointBounds41810 : List (Nat × Nat × Nat) := [(5484070912,109421868061195,109422253894986)]
theorem point_links_checked41810 : (cuts41810.take 1).map (fun c => (5484052481-1+2*2^10*c.k,109421825819905+c.lower,109422211653673+c.upper)) = pointBounds41810 := by
 decide +kernel
def cuts41811 : List PrefixCut := [⟨29,136010116,136010199⟩,
⟨64,303531515,303531697⟩]
theorem checked41811 : checkPrefixCuts (2^48) 5484183553 10 Manual.Count131072.C041811.packed 64 cuts41811 = true := by
 decide +kernel
def pointBounds41811 : List (Nat × Nat × Nat) := [(5484242944,109422263777730,109422649611759)]
theorem point_links_checked41811 : (cuts41811.take 1).map (fun c => (5484183553-1+2*2^10*c.k,109422127767614+c.lower,109422513601560+c.upper)) = pointBounds41811 := by
 decide +kernel
def cuts41812 : List PrefixCut := [⟨49,227412895,227413027⟩,
⟨64,297673452,297673626⟩]
theorem checked41812 : checkPrefixCuts (2^48) 5484314625 10 Manual.Count131072.C041812.packed 64 cuts41812 = true := by
 decide +kernel
def pointBounds41812 : List (Nat × Nat × Nat) := [(5484414976,109422658712024,109423044546284)]
theorem point_links_checked41812 : (cuts41812.take 1).map (fun c => (5484314625-1+2*2^10*c.k,109422431299129+c.lower,109422817133257+c.upper)) = pointBounds41812 := by
 decide +kernel
def cuts41813 : List PrefixCut := [⟨64,298076934,298077117⟩]
theorem checked41813 : checkPrefixCuts (2^48) 5484445697 10 Manual.Count131072.C041813.packed 64 cuts41813 = true := by
 decide +kernel
def cuts41814 : List PrefixCut := [⟨5,22478651,22478664⟩,
⟨64,296068286,296068466⟩]
theorem checked41814 : checkPrefixCuts (2^48) 5484576769 10 Manual.Count131072.C041814.packed 64 cuts41814 = true := by
 decide +kernel
def pointBounds41814 : List (Nat × Nat × Nat) := [(5484587008,109423049528166,109423435362664)]
theorem point_links_checked41814 : (cuts41814.take 1).map (fun c => (5484576769-1+2*2^10*c.k,109423027049515+c.lower,109423412884000+c.upper)) = pointBounds41814 := by
 decide +kernel
def cuts41815 : List PrefixCut := [⟨25,117111562,117111631⟩,
⟨64,297395532,297395708⟩]
theorem checked41815 : checkPrefixCuts (2^48) 5484707841 10 Manual.Count131072.C041815.packed 64 cuts41815 = true := by
 decide +kernel
def pointBounds41815 : List (Nat × Nat × Nat) := [(5484759040,109423440229363,109423826064097)]
theorem point_links_checked41815 : (cuts41815.take 1).map (fun c => (5484707841-1+2*2^10*c.k,109423323117801+c.lower,109423708952466+c.upper)) = pointBounds41815 := by
 decide +kernel
def cuts41816 : List PrefixCut := [⟨45,212970882,212971009⟩,
⟨64,302571535,302571715⟩]
theorem checked41816 : checkPrefixCuts (2^48) 5484838913 10 Manual.Count131072.C041816.packed 64 cuts41816 = true := by
 decide +kernel
def pointBounds41816 : List (Nat × Nat × Nat) := [(5484931072,109423833484215,109424219319183)]
theorem point_links_checked41816 : (cuts41816.take 1).map (fun c => (5484838913-1+2*2^10*c.k,109423620513333+c.lower,109424006348174+c.upper)) = pointBounds41816 := by
 decide +kernel
def cuts41817 : List PrefixCut := [⟨64,301640584,301640763⟩]
theorem checked41817 : checkPrefixCuts (2^48) 5484969985 10 Manual.Count131072.C041817.packed 64 cuts41817 = true := by
 decide +kernel
def cuts41818 : List PrefixCut := [⟨1,4053984,4053987⟩,
⟨64,298503118,298503295⟩]
theorem checked41818 : checkPrefixCuts (2^48) 5485101057 10 Manual.Count131072.C041818.packed 64 cuts41818 = true := by
 decide +kernel
def pointBounds41818 : List (Nat × Nat × Nat) := [(5485103104,109424228779436,109424614614639)]
theorem point_links_checked41818 : (cuts41818.take 1).map (fun c => (5485101057-1+2*2^10*c.k,109424224725452+c.lower,109424610560652+c.upper)) = pointBounds41818 := by
 decide +kernel
def cuts41819 : List PrefixCut := [⟨21,101244166,101244227⟩,
⟨64,303268272,303268452⟩]
theorem checked41819 : checkPrefixCuts (2^48) 5485232129 10 Manual.Count131072.C041819.packed 64 cuts41819 = true := by
 decide +kernel
def pointBounds41819 : List (Nat × Nat × Nat) := [(5485275136,109424624472736,109425010308174)]
theorem point_links_checked41819 : (cuts41819.take 1).map (fun c => (5485232129-1+2*2^10*c.k,109424523228570+c.lower,109424909063947+c.upper)) = pointBounds41819 := by
 decide +kernel
def cuts41820 : List PrefixCut := [⟨41,195914652,195914766⟩,
⟨64,304954358,304954537⟩]
theorem checked41820 : checkPrefixCuts (2^48) 5485363201 10 Manual.Count131072.C041820.packed 64 cuts41820 = true := by
 decide +kernel
def pointBounds41820 : List (Nat × Nat × Nat) := [(5485447168,109425022411494,109425408247165)]
theorem point_links_checked41820 : (cuts41820.take 1).map (fun c => (5485363201-1+2*2^10*c.k,109424826496842+c.lower,109425212332399+c.upper)) = pointBounds41820 := by
 decide +kernel
def cuts41821 : List PrefixCut := [⟨61,286423570,286423740⟩,
⟨64,299713220,299713397⟩]
theorem checked41821 : checkPrefixCuts (2^48) 5485494273 10 Manual.Count131072.C041821.packed 64 cuts41821 = true := by
 decide +kernel
def pointBounds41821 : List (Nat × Nat × Nat) := [(5485619200,109425417874770,109425803710676)]
theorem point_links_checked41821 : (cuts41821.take 1).map (fun c => (5485494273-1+2*2^10*c.k,109425131451200+c.lower,109425517286936+c.upper)) = pointBounds41821 := by
 decide +kernel
def cuts41822 : List PrefixCut := [⟨64,304170116,304170292⟩]
theorem checked41822 : checkPrefixCuts (2^48) 5485625345 10 Manual.Count131072.C041822.packed 64 cuts41822 = true := by
 decide +kernel
def cuts41823 : List PrefixCut := [⟨17,79427834,79427881⟩,
⟨64,300006790,300006960⟩]
theorem checked41823 : checkPrefixCuts (2^48) 5485756417 10 Manual.Count131072.C041823.packed 64 cuts41823 = true := by
 decide +kernel
def pointBounds41823 : List (Nat × Nat × Nat) := [(5485791232,109425814762370,109426200598506)]
theorem point_links_checked41823 : (cuts41823.take 1).map (fun c => (5485756417-1+2*2^10*c.k,109425735334536+c.lower,109426121170625+c.upper)) = pointBounds41823 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000056
