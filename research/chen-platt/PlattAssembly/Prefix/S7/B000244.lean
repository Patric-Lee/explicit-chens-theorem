import PlattAssemblyKernel
import PlattCertificates.Count131072.C067808
import PlattCertificates.Count131072.C067809
import PlattCertificates.Count131072.C067810
import PlattCertificates.Count131072.C067811
import PlattCertificates.Count131072.C067812
import PlattCertificates.Count131072.C067813
import PlattCertificates.Count131072.C067814
import PlattCertificates.Count131072.C067815
import PlattCertificates.Count131072.C067816
import PlattCertificates.Count131072.C067817
import PlattCertificates.Count131072.C067818
import PlattCertificates.Count131072.C067819
import PlattCertificates.Count131072.C067820
import PlattCertificates.Count131072.C067821
import PlattCertificates.Count131072.C067822
import PlattCertificates.Count131072.C067823
import PlattCertificates.Count131072.C067824
import PlattCertificates.Count131072.C067825
import PlattCertificates.Count131072.C067826
import PlattCertificates.Count131072.C067827
import PlattCertificates.Count131072.C067828
import PlattCertificates.Count131072.C067829
import PlattCertificates.Count131072.C067830
import PlattCertificates.Count131072.C067831
import PlattCertificates.Count131072.C067832
import PlattCertificates.Count131072.C067833
import PlattCertificates.Count131072.C067834
import PlattCertificates.Count131072.C067835
import PlattCertificates.Count131072.C067836
import PlattCertificates.Count131072.C067837
import PlattCertificates.Count131072.C067838
import PlattCertificates.Count131072.C067839
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000244
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67808 : List PrefixCut := [⟨64,179836704,179836809⟩]
theorem checked67808 : checkPrefixCuts (2^48) 8891662337 10 Manual.Count131072.C067808.packed 64 cuts67808 = true := by
 decide +kernel
def cuts67809 : List PrefixCut := [⟨61,172553357,172553458⟩,
⟨64,180878655,180878761⟩]
theorem checked67809 : checkPrefixCuts (2^48) 8891793409 10 Manual.Count131072.C067809.packed 64 cuts67809 = true := by
 decide +kernel
def pointBounds67809 : List (Nat × Nat × Nat) := [(8891918336,115423643372534,115424032648992)]
theorem point_links_checked67809 : (cuts67809.take 1).map (fun c => (8891793409-1+2*2^10*c.k,115423470819177+c.lower,115423860095534+c.upper)) = pointBounds67809 := by
 decide +kernel
def cuts67810 : List PrefixCut := [⟨64,182585362,182585471⟩]
theorem checked67810 : checkPrefixCuts (2^48) 8891924481 10 Manual.Count131072.C067810.packed 64 cuts67810 = true := by
 decide +kernel
def cuts67811 : List PrefixCut := [⟨64,180081965,180082068⟩]
theorem checked67811 : checkPrefixCuts (2^48) 8892055553 10 Manual.Count131072.C067811.packed 64 cuts67811 = true := by
 decide +kernel
def cuts67812 : List PrefixCut := [⟨5,13642945,13642952⟩,
⟨64,181756970,181757076⟩]
theorem checked67812 : checkPrefixCuts (2^48) 8892186625 10 Manual.Count131072.C067812.packed 64 cuts67812 = true := by
 decide +kernel
def pointBounds67812 : List (Nat × Nat × Nat) := [(8892196864,115424028008104,115424417284786)]
theorem point_links_checked67812 : (cuts67812.take 1).map (fun c => (8892186625-1+2*2^10*c.k,115424014365159+c.lower,115424403641834+c.upper)) = pointBounds67812 := by
 decide +kernel
def cuts67813 : List PrefixCut := [⟨64,180139964,180140067⟩]
theorem checked67813 : checkPrefixCuts (2^48) 8892317697 10 Manual.Count131072.C067813.packed 64 cuts67813 = true := by
 decide +kernel
def cuts67814 : List PrefixCut := [⟨13,36939287,36939308⟩,
⟨64,181403426,181403532⟩]
theorem checked67814 : checkPrefixCuts (2^48) 8892448769 10 Manual.Count131072.C067814.packed 64 cuts67814 = true := by
 decide +kernel
def pointBounds67814 : List (Nat × Nat × Nat) := [(8892475392,115424413201380,115424802478285)]
theorem point_links_checked67814 : (cuts67814.take 1).map (fun c => (8892448769-1+2*2^10*c.k,115424376262093+c.lower,115424765538977+c.upper)) = pointBounds67814 := by
 decide +kernel
def cuts67815 : List PrefixCut := [⟨64,182698515,182698623⟩]
theorem checked67815 : checkPrefixCuts (2^48) 8892579841 10 Manual.Count131072.C067815.packed 64 cuts67815 = true := by
 decide +kernel
def cuts67816 : List PrefixCut := [⟨21,58208469,58208501⟩,
⟨64,180290253,180290359⟩]
theorem checked67816 : checkPrefixCuts (2^48) 8892710913 10 Manual.Count131072.C067816.packed 64 cuts67816 = true := by
 decide +kernel
def pointBounds67816 : List (Nat × Nat × Nat) := [(8892753920,115424798572503,115425187849633)]
theorem point_links_checked67816 : (cuts67816.take 1).map (fun c => (8892710913-1+2*2^10*c.k,115424740364034+c.lower,115425129641132+c.upper)) = pointBounds67816 := by
 decide +kernel
def cuts67817 : List PrefixCut := [⟨64,180350892,180351004⟩]
theorem checked67817 : checkPrefixCuts (2^48) 8892841985 10 Manual.Count131072.C067817.packed 64 cuts67817 = true := by
 decide +kernel
def cuts67818 : List PrefixCut := [⟨29,82388275,82388325⟩,
⟨64,181772549,181772660⟩]
theorem checked67818 : checkPrefixCuts (2^48) 8892973057 10 Manual.Count131072.C067818.packed 64 cuts67818 = true := by
 decide +kernel
def pointBounds67818 : List (Nat × Nat × Nat) := [(8893032448,115425183393454,115425572670820)]
theorem point_links_checked67818 : (cuts67818.take 1).map (fun c => (8892973057-1+2*2^10*c.k,115425101005179+c.lower,115425490282495+c.upper)) = pointBounds67818 := by
 decide +kernel
def cuts67819 : List PrefixCut := [⟨64,181516678,181516781⟩]
theorem checked67819 : checkPrefixCuts (2^48) 8893104129 10 Manual.Count131072.C067819.packed 64 cuts67819 = true := by
 decide +kernel
def cuts67820 : List PrefixCut := [⟨37,104414390,104414448⟩,
⟨64,178918677,178918784⟩]
theorem checked67820 : checkPrefixCuts (2^48) 8893235201 10 Manual.Count131072.C067820.packed 64 cuts67820 = true := by
 decide +kernel
def pointBounds67820 : List (Nat × Nat × Nat) := [(8893310976,115425568708796,115425957986384)]
theorem point_links_checked67820 : (cuts67820.take 1).map (fun c => (8893235201-1+2*2^10*c.k,115425464294406+c.lower,115425853571936+c.upper)) = pointBounds67820 := by
 decide +kernel
def cuts67821 : List PrefixCut := [⟨64,181922763,181922874⟩]
theorem checked67821 : checkPrefixCuts (2^48) 8893366273 10 Manual.Count131072.C067821.packed 64 cuts67821 = true := by
 decide +kernel
def cuts67822 : List PrefixCut := [⟨45,127072148,127072225⟩,
⟨64,180717403,180717512⟩]
theorem checked67822 : checkPrefixCuts (2^48) 8893497345 10 Manual.Count131072.C067822.packed 64 cuts67822 = true := by
 decide +kernel
def pointBounds67822 : List (Nat × Nat × Nat) := [(8893589504,115425952207994,115426341485819)]
theorem point_links_checked67822 : (cuts67822.take 1).map (fun c => (8893497345-1+2*2^10*c.k,115425825135846+c.lower,115426214413594+c.upper)) = pointBounds67822 := by
 decide +kernel
def cuts67823 : List PrefixCut := [⟨64,180967944,180968049⟩]
theorem checked67823 : checkPrefixCuts (2^48) 8893628417 10 Manual.Count131072.C067823.packed 64 cuts67823 = true := by
 decide +kernel
def cuts67824 : List PrefixCut := [⟨53,151279314,151279403⟩,
⟨64,182674287,182674395⟩]
theorem checked67824 : checkPrefixCuts (2^48) 8893759489 10 Manual.Count131072.C067824.packed 64 cuts67824 = true := by
 decide +kernel
def pointBounds67824 : List (Nat × Nat × Nat) := [(8893868032,115426338100507,115426727378558)]
theorem point_links_checked67824 : (cuts67824.take 1).map (fun c => (8893759489-1+2*2^10*c.k,115426186821193+c.lower,115426576099155+c.upper)) = pointBounds67824 := by
 decide +kernel
def cuts67825 : List PrefixCut := [⟨64,181215788,181215894⟩]
theorem checked67825 : checkPrefixCuts (2^48) 8893890561 10 Manual.Count131072.C067825.packed 64 cuts67825 = true := by
 decide +kernel
def cuts67826 : List PrefixCut := [⟨61,171402479,171402578⟩,
⟨64,179504161,179504265⟩]
theorem checked67826 : checkPrefixCuts (2^48) 8894021633 10 Manual.Count131072.C067826.packed 64 cuts67826 = true := by
 decide +kernel
def pointBounds67826 : List (Nat × Nat × Nat) := [(8894146560,115426722113747,115427111392022)]
theorem point_links_checked67826 : (cuts67826.take 1).map (fun c => (8894021633-1+2*2^10*c.k,115426550711268+c.lower,115426939989444+c.upper)) = pointBounds67826 := by
 decide +kernel
def cuts67827 : List PrefixCut := [⟨64,180292686,180292792⟩]
theorem checked67827 : checkPrefixCuts (2^48) 8894152705 10 Manual.Count131072.C067827.packed 64 cuts67827 = true := by
 decide +kernel
def cuts67828 : List PrefixCut := [⟨64,181524252,181524359⟩]
theorem checked67828 : checkPrefixCuts (2^48) 8894283777 10 Manual.Count131072.C067828.packed 64 cuts67828 = true := by
 decide +kernel
def cuts67829 : List PrefixCut := [⟨5,14019282,14019288⟩,
⟨64,179369640,179369744⟩]
theorem checked67829 : checkPrefixCuts (2^48) 8894414849 10 Manual.Count131072.C067829.packed 64 cuts67829 = true := by
 decide +kernel
def pointBounds67829 : List (Nat × Nat × Nat) := [(8894425088,115427106051649,115427495330148)]
theorem point_links_checked67829 : (cuts67829.take 1).map (fun c => (8894414849-1+2*2^10*c.k,115427092032367+c.lower,115427481310860+c.upper)) = pointBounds67829 := by
 decide +kernel
def cuts67830 : List PrefixCut := [⟨64,181708752,181708860⟩]
theorem checked67830 : checkPrefixCuts (2^48) 8894545921 10 Manual.Count131072.C067830.packed 64 cuts67830 = true := by
 decide +kernel
def cuts67831 : List PrefixCut := [⟨13,38069261,38069285⟩,
⟨64,182971896,182972003⟩]
theorem checked67831 : checkPrefixCuts (2^48) 8894676993 10 Manual.Count131072.C067831.packed 64 cuts67831 = true := by
 decide +kernel
def pointBounds67831 : List (Nat × Nat × Nat) := [(8894703616,115427491180020,115427880458749)]
theorem point_links_checked67831 : (cuts67831.take 1).map (fun c => (8894676993-1+2*2^10*c.k,115427453110759+c.lower,115427842389464+c.upper)) = pointBounds67831 := by
 decide +kernel
def cuts67832 : List PrefixCut := [⟨64,179076905,179077011⟩]
theorem checked67832 : checkPrefixCuts (2^48) 8894808065 10 Manual.Count131072.C067832.packed 64 cuts67832 = true := by
 decide +kernel
def cuts67833 : List PrefixCut := [⟨21,59459656,59459693⟩,
⟨64,179359064,179359171⟩]
theorem checked67833 : checkPrefixCuts (2^48) 8894939137 10 Manual.Count131072.C067833.packed 64 cuts67833 = true := by
 decide +kernel
def pointBounds67833 : List (Nat × Nat × Nat) := [(8894982144,115427874619216,115428263898171)]
theorem point_links_checked67833 : (cuts67833.take 1).map (fun c => (8894939137-1+2*2^10*c.k,115427815159560+c.lower,115428204438478+c.upper)) = pointBounds67833 := by
 decide +kernel
def cuts67834 : List PrefixCut := [⟨64,182109433,182109537⟩]
theorem checked67834 : checkPrefixCuts (2^48) 8895070209 10 Manual.Count131072.C067834.packed 64 cuts67834 = true := by
 decide +kernel
def cuts67835 : List PrefixCut := [⟨29,82462564,82462614⟩,
⟨64,181727011,181727120⟩]
theorem checked67835 : checkPrefixCuts (2^48) 8895201281 10 Manual.Count131072.C067835.packed 64 cuts67835 = true := by
 decide +kernel
def pointBounds67835 : List (Nat × Nat × Nat) := [(8895260672,115428259090621,115428648369800)]
theorem point_links_checked67835 : (cuts67835.take 1).map (fun c => (8895201281-1+2*2^10*c.k,115428176628057+c.lower,115428565907186+c.upper)) = pointBounds67835 := by
 decide +kernel
def cuts67836 : List PrefixCut := [⟨64,184540544,184540646⟩]
theorem checked67836 : checkPrefixCuts (2^48) 8895332353 10 Manual.Count131072.C067836.packed 64 cuts67836 = true := by
 decide +kernel
def cuts67837 : List PrefixCut := [⟨37,103787031,103787089⟩,
⟨64,179918048,179918149⟩]
theorem checked67837 : checkPrefixCuts (2^48) 8895463425 10 Manual.Count131072.C067837.packed 64 cuts67837 = true := by
 decide +kernel
def pointBounds67837 : List (Nat × Nat × Nat) := [(8895539200,115428646682643,115429035962041)]
theorem point_links_checked67837 : (cuts67837.take 1).map (fun c => (8895463425-1+2*2^10*c.k,115428542895612+c.lower,115428932174952+c.upper)) = pointBounds67837 := by
 decide +kernel
def cuts67838 : List PrefixCut := [⟨64,180833004,180833112⟩]
theorem checked67838 : checkPrefixCuts (2^48) 8895594497 10 Manual.Count131072.C067838.packed 64 cuts67838 = true := by
 decide +kernel
def cuts67839 : List PrefixCut := [⟨45,127103608,127103683⟩,
⟨64,180988560,180988667⟩]
theorem checked67839 : checkPrefixCuts (2^48) 8895725569 10 Manual.Count131072.C067839.packed 64 cuts67839 = true := by
 decide +kernel
def pointBounds67839 : List (Nat × Nat × Nat) := [(8895817728,115429030750272,115429420029896)]
theorem point_links_checked67839 : (cuts67839.take 1).map (fun c => (8895725569-1+2*2^10*c.k,115428903646664+c.lower,115429292926213+c.upper)) = pointBounds67839 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000244
