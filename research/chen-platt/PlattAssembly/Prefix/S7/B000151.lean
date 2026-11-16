import PlattAssemblyKernel
import PlattCertificates.Count131072.C064832
import PlattCertificates.Count131072.C064833
import PlattCertificates.Count131072.C064834
import PlattCertificates.Count131072.C064835
import PlattCertificates.Count131072.C064836
import PlattCertificates.Count131072.C064837
import PlattCertificates.Count131072.C064838
import PlattCertificates.Count131072.C064839
import PlattCertificates.Count131072.C064840
import PlattCertificates.Count131072.C064841
import PlattCertificates.Count131072.C064842
import PlattCertificates.Count131072.C064843
import PlattCertificates.Count131072.C064844
import PlattCertificates.Count131072.C064845
import PlattCertificates.Count131072.C064846
import PlattCertificates.Count131072.C064847
import PlattCertificates.Count131072.C064848
import PlattCertificates.Count131072.C064849
import PlattCertificates.Count131072.C064850
import PlattCertificates.Count131072.C064851
import PlattCertificates.Count131072.C064852
import PlattCertificates.Count131072.C064853
import PlattCertificates.Count131072.C064854
import PlattCertificates.Count131072.C064855
import PlattCertificates.Count131072.C064856
import PlattCertificates.Count131072.C064857
import PlattCertificates.Count131072.C064858
import PlattCertificates.Count131072.C064859
import PlattCertificates.Count131072.C064860
import PlattCertificates.Count131072.C064861
import PlattCertificates.Count131072.C064862
import PlattCertificates.Count131072.C064863
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000151
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64832 : List PrefixCut := [⟨12,35293601,35293622⟩,
⟨64,190438582,190438693⟩]
theorem checked64832 : checkPrefixCuts (2^48) 8501592065 10 Manual.Count131072.C064832.packed 64 cuts64832 = true := by
 decide +kernel
def pointBounds64832 : List (Nat × Nat × Nat) := [(8501616640,114871593543104,114871982498732)]
theorem point_links_checked64832 : (cuts64832.take 1).map (fun c => (8501592065-1+2*2^10*c.k,114871558249503+c.lower,114871947205110+c.upper)) = pointBounds64832 := by
 decide +kernel
def cuts64833 : List PrefixCut := [⟨64,193183587,193183698⟩]
theorem checked64833 : checkPrefixCuts (2^48) 8501723137 10 Manual.Count131072.C064833.packed 64 cuts64833 = true := by
 decide +kernel
def cuts64834 : List PrefixCut := [⟨14,40788338,40788360⟩,
⟨64,189340173,189340276⟩]
theorem checked64834 : checkPrefixCuts (2^48) 8501854209 10 Manual.Count131072.C064834.packed 64 cuts64834 = true := by
 decide +kernel
def pointBounds64834 : List (Nat × Nat × Nat) := [(8501882880,114871982660010,114872371615861)]
theorem point_links_checked64834 : (cuts64834.take 1).map (fun c => (8501854209-1+2*2^10*c.k,114871941871672+c.lower,114872330827501+c.upper)) = pointBounds64834 := by
 decide +kernel
def cuts64835 : List PrefixCut := [⟨64,189635206,189635316⟩]
theorem checked64835 : checkPrefixCuts (2^48) 8501985281 10 Manual.Count131072.C064835.packed 64 cuts64835 = true := by
 decide +kernel
def cuts64836 : List PrefixCut := [⟨16,48103580,48103608⟩,
⟨64,190791002,190791113⟩]
theorem checked64836 : checkPrefixCuts (2^48) 8502116353 10 Manual.Count131072.C064836.packed 64 cuts64836 = true := by
 decide +kernel
def pointBounds64836 : List (Nat × Nat × Nat) := [(8502149120,114872368950631,114872757906701)]
theorem point_links_checked64836 : (cuts64836.take 1).map (fun c => (8502116353-1+2*2^10*c.k,114872320847051+c.lower,114872709803093+c.upper)) = pointBounds64836 := by
 decide +kernel
def cuts64837 : List PrefixCut := [⟨64,187444375,187444492⟩]
theorem checked64837 : checkPrefixCuts (2^48) 8502247425 10 Manual.Count131072.C064837.packed 64 cuts64837 = true := by
 decide +kernel
def cuts64838 : List PrefixCut := [⟨18,54921790,54921823⟩,
⟨64,189957506,189957620⟩]
theorem checked64838 : checkPrefixCuts (2^48) 8502378497 10 Manual.Count131072.C064838.packed 64 cuts64838 = true := by
 decide +kernel
def pointBounds64838 : List (Nat × Nat × Nat) := [(8502415360,114872754004218,114873142960521)]
theorem point_links_checked64838 : (cuts64838.take 1).map (fun c => (8502378497-1+2*2^10*c.k,114872699082428+c.lower,114873088038698+c.upper)) = pointBounds64838 := by
 decide +kernel
def cuts64839 : List PrefixCut := [⟨64,191080127,191080239⟩]
theorem checked64839 : checkPrefixCuts (2^48) 8502509569 10 Manual.Count131072.C064839.packed 64 cuts64839 = true := by
 decide +kernel
def cuts64840 : List PrefixCut := [⟨20,57899470,57899503⟩,
⟨64,187336395,187336501⟩]
theorem checked64840 : checkPrefixCuts (2^48) 8502640641 10 Manual.Count131072.C064840.packed 64 cuts64840 = true := by
 decide +kernel
def pointBounds64840 : List (Nat × Nat × Nat) := [(8502681600,114873138019531,114873526976060)]
theorem point_links_checked64840 : (cuts64840.take 1).map (fun c => (8502640641-1+2*2^10*c.k,114873080120061+c.lower,114873469076557+c.upper)) = pointBounds64840 := by
 decide +kernel
def cuts64841 : List PrefixCut := [⟨64,190842506,190842617⟩]
theorem checked64841 : checkPrefixCuts (2^48) 8502771713 10 Manual.Count131072.C064841.packed 64 cuts64841 = true := by
 decide +kernel
def cuts64842 : List PrefixCut := [⟨22,65213504,65213540⟩,
⟨64,192925051,192925154⟩]
theorem checked64842 : checkPrefixCuts (2^48) 8502902785 10 Manual.Count131072.C064842.packed 64 cuts64842 = true := by
 decide +kernel
def pointBounds64842 : List (Nat × Nat × Nat) := [(8502947840,114873523512466,114873912469215)]
theorem point_links_checked64842 : (cuts64842.take 1).map (fun c => (8502902785-1+2*2^10*c.k,114873458298962+c.lower,114873847255675+c.upper)) = pointBounds64842 := by
 decide +kernel
def cuts64843 : List PrefixCut := [⟨64,189280801,189280911⟩]
theorem checked64843 : checkPrefixCuts (2^48) 8503033857 10 Manual.Count131072.C064843.packed 64 cuts64843 = true := by
 decide +kernel
def cuts64844 : List PrefixCut := [⟨24,72858104,72858144⟩,
⟨64,192223983,192224091⟩]
theorem checked64844 : checkPrefixCuts (2^48) 8503164929 10 Manual.Count131072.C064844.packed 64 cuts64844 = true := by
 decide +kernel
def pointBounds64844 : List (Nat × Nat × Nat) := [(8503214080,114873913362918,114874302319884)]
theorem point_links_checked64844 : (cuts64844.take 1).map (fun c => (8503164929-1+2*2^10*c.k,114873840504814+c.lower,114874229461740+c.upper)) = pointBounds64844 := by
 decide +kernel
def cuts64845 : List PrefixCut := [⟨64,189142550,189142660⟩]
theorem checked64845 : checkPrefixCuts (2^48) 8503296001 10 Manual.Count131072.C064845.packed 64 cuts64845 = true := by
 decide +kernel
def cuts64846 : List PrefixCut := [⟨26,76761784,76761828⟩,
⟨64,193045561,193045669⟩]
theorem checked64846 : checkPrefixCuts (2^48) 8503427073 10 Manual.Count131072.C064846.packed 64 cuts64846 = true := by
 decide +kernel
def pointBounds64846 : List (Nat × Nat × Nat) := [(8503480320,114874298633131,114874687590319)]
theorem point_links_checked64846 : (cuts64846.take 1).map (fun c => (8503427073-1+2*2^10*c.k,114874221871347+c.lower,114874610828491+c.upper)) = pointBounds64846 := by
 decide +kernel
def cuts64847 : List PrefixCut := [⟨64,189931132,189931244⟩]
theorem checked64847 : checkPrefixCuts (2^48) 8503558145 10 Manual.Count131072.C064847.packed 64 cuts64847 = true := by
 decide +kernel
def cuts64848 : List PrefixCut := [⟨28,82287134,82287182⟩,
⟨64,188902109,188902219⟩]
theorem checked64848 : checkPrefixCuts (2^48) 8503689217 10 Manual.Count131072.C064848.packed 64 cuts64848 = true := by
 decide +kernel
def pointBounds64848 : List (Nat × Nat × Nat) := [(8503746560,114874687135174,114875076092586)]
theorem point_links_checked64848 : (cuts64848.take 1).map (fun c => (8503689217-1+2*2^10*c.k,114874604848040+c.lower,114874993805404+c.upper)) = pointBounds64848 := by
 decide +kernel
def cuts64849 : List PrefixCut := [⟨64,188468905,188469015⟩]
theorem checked64849 : checkPrefixCuts (2^48) 8503820289 10 Manual.Count131072.C064849.packed 64 cuts64849 = true := by
 decide +kernel
def cuts64850 : List PrefixCut := [⟨30,88805118,88805173⟩,
⟨64,189392773,189392891⟩]
theorem checked64850 : checkPrefixCuts (2^48) 8503951361 10 Manual.Count131072.C064850.packed 64 cuts64850 = true := by
 decide +kernel
def pointBounds64850 : List (Nat × Nat × Nat) := [(8504012800,114875071024172,114875459981811)]
theorem point_links_checked64850 : (cuts64850.take 1).map (fun c => (8503951361-1+2*2^10*c.k,114874982219054+c.lower,114875371176638+c.upper)) = pointBounds64850 := by
 decide +kernel
def cuts64851 : List PrefixCut := [⟨64,189456045,189456157⟩]
theorem checked64851 : checkPrefixCuts (2^48) 8504082433 10 Manual.Count131072.C064851.packed 64 cuts64851 = true := by
 decide +kernel
def cuts64852 : List PrefixCut := [⟨32,95289600,95289659⟩,
⟨64,189320753,189320862⟩]
theorem checked64852 : checkPrefixCuts (2^48) 8504213505 10 Manual.Count131072.C064852.packed 64 cuts64852 = true := by
 decide +kernel
def pointBounds64852 : List (Nat × Nat × Nat) := [(8504279040,114875456357472,114875845315345)]
theorem point_links_checked64852 : (cuts64852.take 1).map (fun c => (8504213505-1+2*2^10*c.k,114875361067872+c.lower,114875750025686+c.upper)) = pointBounds64852 := by
 decide +kernel
def cuts64853 : List PrefixCut := [⟨64,188622778,188622885⟩]
theorem checked64853 : checkPrefixCuts (2^48) 8504344577 10 Manual.Count131072.C064853.packed 64 cuts64853 = true := by
 decide +kernel
def cuts64854 : List PrefixCut := [⟨34,101310318,101310377⟩,
⟨64,190142333,190142441⟩]
theorem checked64854 : checkPrefixCuts (2^48) 8504475649 10 Manual.Count131072.C064854.packed 64 cuts64854 = true := by
 decide +kernel
def pointBounds64854 : List (Nat × Nat × Nat) := [(8504545280,114875840321721,114876229279810)]
theorem point_links_checked64854 : (cuts64854.take 1).map (fun c => (8504475649-1+2*2^10*c.k,114875739011403+c.lower,114876127969433+c.upper)) = pointBounds64854 := by
 decide +kernel
def cuts64855 : List PrefixCut := [⟨64,188319102,188319213⟩]
theorem checked64855 : checkPrefixCuts (2^48) 8504606721 10 Manual.Count131072.C064855.packed 64 cuts64855 = true := by
 decide +kernel
def cuts64856 : List PrefixCut := [⟨36,108257352,108257413⟩,
⟨64,189706233,189706341⟩]
theorem checked64856 : checkPrefixCuts (2^48) 8504737793 10 Manual.Count131072.C064856.packed 64 cuts64856 = true := by
 decide +kernel
def pointBounds64856 : List (Nat × Nat × Nat) := [(8504811520,114876225730190,114876614688500)]
theorem point_links_checked64856 : (cuts64856.take 1).map (fun c => (8504737793-1+2*2^10*c.k,114876117472838+c.lower,114876506431087+c.upper)) = pointBounds64856 := by
 decide +kernel
def cuts64857 : List PrefixCut := [⟨64,191788321,191788426⟩]
theorem checked64857 : checkPrefixCuts (2^48) 8504868865 10 Manual.Count131072.C064857.packed 64 cuts64857 = true := by
 decide +kernel
def cuts64858 : List PrefixCut := [⟨38,113019686,113019748⟩,
⟨64,190693228,190693335⟩]
theorem checked64858 : checkPrefixCuts (2^48) 8504999937 10 Manual.Count131072.C064858.packed 64 cuts64858 = true := by
 decide +kernel
def pointBounds64858 : List (Nat × Nat × Nat) := [(8505077760,114876611987078,114877000945602)]
theorem point_links_checked64858 : (cuts64858.take 1).map (fun c => (8504999937-1+2*2^10*c.k,114876498967392+c.lower,114876887925854+c.upper)) = pointBounds64858 := by
 decide +kernel
def cuts64859 : List PrefixCut := [⟨64,188439860,188439969⟩]
theorem checked64859 : checkPrefixCuts (2^48) 8505131009 10 Manual.Count131072.C064859.packed 64 cuts64859 = true := by
 decide +kernel
def cuts64860 : List PrefixCut := [⟨40,119370231,119370299⟩,
⟨64,191448508,191448618⟩]
theorem checked64860 : checkPrefixCuts (2^48) 8505262081 10 Manual.Count131072.C064860.packed 64 cuts64860 = true := by
 decide +kernel
def pointBounds64860 : List (Nat × Nat × Nat) := [(8505344000,114876997470711,114877386429457)]
theorem point_links_checked64860 : (cuts64860.take 1).map (fun c => (8505262081-1+2*2^10*c.k,114876878100480+c.lower,114877267059158+c.upper)) = pointBounds64860 := by
 decide +kernel
def cuts64861 : List PrefixCut := [⟨64,191213909,191214021⟩]
theorem checked64861 : checkPrefixCuts (2^48) 8505393153 10 Manual.Count131072.C064861.packed 64 cuts64861 = true := by
 decide +kernel
def cuts64862 : List PrefixCut := [⟨42,122940562,122940634⟩,
⟨64,188795163,188795272⟩]
theorem checked64862 : checkPrefixCuts (2^48) 8505524225 10 Manual.Count131072.C064862.packed 64 cuts64862 = true := by
 decide +kernel
def pointBounds64862 : List (Nat × Nat × Nat) := [(8505610240,114877383703459,114877772662431)]
theorem point_links_checked64862 : (cuts64862.take 1).map (fun c => (8505524225-1+2*2^10*c.k,114877260762897+c.lower,114877649721797+c.upper)) = pointBounds64862 := by
 decide +kernel
def cuts64863 : List PrefixCut := [⟨64,189884305,189884417⟩]
theorem checked64863 : checkPrefixCuts (2^48) 8505655297 10 Manual.Count131072.C064863.packed 64 cuts64863 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000151
