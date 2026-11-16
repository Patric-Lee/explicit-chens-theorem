import PlattAssemblyKernel
import PlattCertificates.Count131072.C058832
import PlattCertificates.Count131072.C058833
import PlattCertificates.Count131072.C058834
import PlattCertificates.Count131072.C058835
import PlattCertificates.Count131072.C058836
import PlattCertificates.Count131072.C058837
import PlattCertificates.Count131072.C058838
import PlattCertificates.Count131072.C058839
import PlattCertificates.Count131072.C058840
import PlattCertificates.Count131072.C058841
import PlattCertificates.Count131072.C058842
import PlattCertificates.Count131072.C058843
import PlattCertificates.Count131072.C058844
import PlattCertificates.Count131072.C058845
import PlattCertificates.Count131072.C058846
import PlattCertificates.Count131072.C058847
import PlattCertificates.Count131072.C058848
import PlattCertificates.Count131072.C058849
import PlattCertificates.Count131072.C058850
import PlattCertificates.Count131072.C058851
import PlattCertificates.Count131072.C058852
import PlattCertificates.Count131072.C058853
import PlattCertificates.Count131072.C058854
import PlattCertificates.Count131072.C058855
import PlattCertificates.Count131072.C058856
import PlattCertificates.Count131072.C058857
import PlattCertificates.Count131072.C058858
import PlattCertificates.Count131072.C058859
import PlattCertificates.Count131072.C058860
import PlattCertificates.Count131072.C058861
import PlattCertificates.Count131072.C058862
import PlattCertificates.Count131072.C058863
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000276
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts58832 : List PrefixCut := [⟨64,207515540,207515659⟩]
theorem checked58832 : checkPrefixCuts (2^48) 7715160065 10 Manual.Count131072.C058832.packed 64 cuts58832 = true := by
 decide +kernel
def cuts58833 : List PrefixCut := [⟨26,84274818,84274866⟩,
⟨64,209846875,209846995⟩]
theorem checked58833 : checkPrefixCuts (2^48) 7715291137 10 Manual.Count131072.C058833.packed 64 cuts58833 = true := by
 decide +kernel
def pointBounds58833 : List (Nat × Nat × Nat) := [(7715344384,113674230000897,113674618269686)]
theorem point_links_checked58833 : (cuts58833.take 1).map (fun c => (7715291137-1+2*2^10*c.k,113674145726079+c.lower,113674533994820+c.upper)) = pointBounds58833 := by
 decide +kernel
def cuts58834 : List PrefixCut := [⟨64,211448512,211448632⟩]
theorem checked58834 : checkPrefixCuts (2^48) 7715422209 10 Manual.Count131072.C058834.packed 64 cuts58834 = true := by
 decide +kernel
def cuts58835 : List PrefixCut := [⟨16,53408788,53408818⟩,
⟨64,213050095,213050212⟩]
theorem checked58835 : checkPrefixCuts (2^48) 7715553281 10 Manual.Count131072.C058835.packed 64 cuts58835 = true := by
 decide +kernel
def pointBounds58835 : List (Nat × Nat × Nat) := [(7715586048,113674620430254,113675008699265)]
theorem point_links_checked58835 : (cuts58835.take 1).map (fun c => (7715553281-1+2*2^10*c.k,113674567021466+c.lower,113674955290447+c.upper)) = pointBounds58835 := by
 decide +kernel
def cuts58836 : List PrefixCut := [⟨64,211952067,211952187⟩]
theorem checked58836 : checkPrefixCuts (2^48) 7715684353 10 Manual.Count131072.C058836.packed 64 cuts58836 = true := by
 decide +kernel
def cuts58837 : List PrefixCut := [⟨6,19954681,19954693⟩,
⟨64,210708139,210708260⟩]
theorem checked58837 : checkPrefixCuts (2^48) 7715815425 10 Manual.Count131072.C058837.packed 64 cuts58837 = true := by
 decide +kernel
def pointBounds58837 : List (Nat × Nat × Nat) := [(7715827712,113675011978309,113675400247539)]
theorem point_links_checked58837 : (cuts58837.take 1).map (fun c => (7715815425-1+2*2^10*c.k,113674992023628+c.lower,113675380292846+c.upper)) = pointBounds58837 := by
 decide +kernel
def cuts58838 : List PrefixCut := [⟨60,196915479,196915588⟩,
⟨64,209792578,209792693⟩]
theorem checked58838 : checkPrefixCuts (2^48) 7715946497 10 Manual.Count131072.C058838.packed 64 cuts58838 = true := by
 decide +kernel
def pointBounds58838 : List (Nat × Nat × Nat) := [(7716069376,113675399647246,113675787916694)]
theorem point_links_checked58838 : (cuts58838.take 1).map (fun c => (7715946497-1+2*2^10*c.k,113675202731767+c.lower,113675591001106+c.upper)) = pointBounds58838 := by
 decide +kernel
def cuts58839 : List PrefixCut := [⟨64,214239431,214239556⟩]
theorem checked58839 : checkPrefixCuts (2^48) 7716077569 10 Manual.Count131072.C058839.packed 64 cuts58839 = true := by
 decide +kernel
def cuts58840 : List PrefixCut := [⟨50,164625899,164625994⟩,
⟨64,209858425,209858544⟩]
theorem checked58840 : checkPrefixCuts (2^48) 7716208641 10 Manual.Count131072.C058840.packed 64 cuts58840 = true := by
 decide +kernel
def pointBounds58840 : List (Nat × Nat × Nat) := [(7716311040,113675791389675,113676179659349)]
theorem point_links_checked58840 : (cuts58840.take 1).map (fun c => (7716208641-1+2*2^10*c.k,113675626763776+c.lower,113676015033355+c.upper)) = pointBounds58840 := by
 decide +kernel
def cuts58841 : List PrefixCut := [⟨64,210803270,210803391⟩]
theorem checked58841 : checkPrefixCuts (2^48) 7716339713 10 Manual.Count131072.C058841.packed 64 cuts58841 = true := by
 decide +kernel
def cuts58842 : List PrefixCut := [⟨40,131864205,131864283⟩,
⟨64,211164447,211164572⟩]
theorem checked58842 : checkPrefixCuts (2^48) 7716470785 10 Manual.Count131072.C058842.packed 64 cuts58842 = true := by
 decide +kernel
def pointBounds58842 : List (Nat × Nat × Nat) := [(7716552704,113676179289676,113676567559573)]
theorem point_links_checked58842 : (cuts58842.take 1).map (fun c => (7716470785-1+2*2^10*c.k,113676047425471+c.lower,113676435695290+c.upper)) = pointBounds58842 := by
 decide +kernel
def cuts58843 : List PrefixCut := [⟨64,209519431,209519548⟩]
theorem checked58843 : checkPrefixCuts (2^48) 7716601857 10 Manual.Count131072.C058843.packed 64 cuts58843 = true := by
 decide +kernel
def cuts58844 : List PrefixCut := [⟨30,99761230,99761286⟩,
⟨64,210172451,210172567⟩]
theorem checked58844 : checkPrefixCuts (2^48) 7716732929 10 Manual.Count131072.C058844.packed 64 cuts58844 = true := by
 decide +kernel
def pointBounds58844 : List (Nat × Nat × Nat) := [(7716794368,113676567870579,113676956140696)]
theorem point_links_checked58844 : (cuts58844.take 1).map (fun c => (7716732929-1+2*2^10*c.k,113676468109349+c.lower,113676856379410+c.upper)) = pointBounds58844 := by
 decide +kernel
def cuts58845 : List PrefixCut := [⟨64,212977438,212977560⟩]
theorem checked58845 : checkPrefixCuts (2^48) 7716864001 10 Manual.Count131072.C058845.packed 64 cuts58845 = true := by
 decide +kernel
def cuts58846 : List PrefixCut := [⟨20,65107127,65107161⟩,
⟨64,208815754,208815869⟩]
theorem checked58846 : checkPrefixCuts (2^48) 7716995073 10 Manual.Count131072.C058846.packed 64 cuts58846 = true := by
 decide +kernel
def pointBounds58846 : List (Nat × Nat × Nat) := [(7717036032,113676956366365,113677344636698)]
theorem point_links_checked58846 : (cuts58846.take 1).map (fun c => (7716995073-1+2*2^10*c.k,113676891259238+c.lower,113677279529537+c.upper)) = pointBounds58846 := by
 decide +kernel
def cuts58847 : List PrefixCut := [⟨64,206259043,206259161⟩]
theorem checked58847 : checkPrefixCuts (2^48) 7717126145 10 Manual.Count131072.C058847.packed 64 cuts58847 = true := by
 decide +kernel
def cuts58848 : List PrefixCut := [⟨10,33993199,33993219⟩,
⟨64,212273609,212273733⟩]
theorem checked58848 : checkPrefixCuts (2^48) 7717257217 10 Manual.Count131072.C058848.packed 64 cuts58848 = true := by
 decide +kernel
def pointBounds58848 : List (Nat × Nat × Nat) := [(7717277696,113677340327234,113677728597786)]
theorem point_links_checked58848 : (cuts58848.take 1).map (fun c => (7717257217-1+2*2^10*c.k,113677306334035+c.lower,113677694604567+c.upper)) = pointBounds58848 := by
 decide +kernel
def cuts58849 : List PrefixCut := [⟨64,207637976,207638098⟩]
theorem checked58849 : checkPrefixCuts (2^48) 7717388289 10 Manual.Count131072.C058849.packed 64 cuts58849 = true := by
 decide +kernel
def pointBounds58849 : List (Nat × Nat × Nat) := [(7717519360,113677726245620,113678114516398)]
theorem point_links_checked58849 : (cuts58849.take 1).map (fun c => (7717388289-1+2*2^10*c.k,113677518607644+c.lower,113677906878300+c.upper)) = pointBounds58849 := by
 decide +kernel
def cuts58850 : List PrefixCut := [⟨64,210151023,210151144⟩]
theorem checked58850 : checkPrefixCuts (2^48) 7717519361 10 Manual.Count131072.C058850.packed 64 cuts58850 = true := by
 decide +kernel
def cuts58851 : List PrefixCut := [⟨54,178490627,178490730⟩,
⟨64,211569831,211569953⟩]
theorem checked58851 : checkPrefixCuts (2^48) 7717650433 10 Manual.Count131072.C058851.packed 64 cuts58851 = true := by
 decide +kernel
def pointBounds58851 : List (Nat × Nat × Nat) := [(7717761024,113678114887270,113678503158272)]
theorem point_links_checked58851 : (cuts58851.take 1).map (fun c => (7717650433-1+2*2^10*c.k,113677936396643+c.lower,113678324667542+c.upper)) = pointBounds58851 := by
 decide +kernel
def cuts58852 : List PrefixCut := [⟨64,210690954,210691078⟩]
theorem checked58852 : checkPrefixCuts (2^48) 7717781505 10 Manual.Count131072.C058852.packed 64 cuts58852 = true := by
 decide +kernel
def cuts58853 : List PrefixCut := [⟨44,144421704,144421787⟩,
⟨64,210577952,210578073⟩]
theorem checked58853 : checkPrefixCuts (2^48) 7717912577 10 Manual.Count131072.C058853.packed 64 cuts58853 = true := by
 decide +kernel
def pointBounds58853 : List (Nat × Nat × Nat) := [(7718002688,113678503079132,113678891350360)]
theorem point_links_checked58853 : (cuts58853.take 1).map (fun c => (7717912577-1+2*2^10*c.k,113678358657428+c.lower,113678746928573+c.upper)) = pointBounds58853 := by
 decide +kernel
def cuts58854 : List PrefixCut := [⟨64,213528410,213528529⟩]
theorem checked58854 : checkPrefixCuts (2^48) 7718043649 10 Manual.Count131072.C058854.packed 64 cuts58854 = true := by
 decide +kernel
def cuts58855 : List PrefixCut := [⟨34,110136185,110136247⟩,
⟨64,210680192,210680313⟩]
theorem checked58855 : checkPrefixCuts (2^48) 7718174721 10 Manual.Count131072.C058855.packed 64 cuts58855 = true := by
 decide +kernel
def pointBounds58855 : List (Nat × Nat × Nat) := [(7718244352,113678892899975,113679281171422)]
theorem point_links_checked58855 : (cuts58855.take 1).map (fun c => (7718174721-1+2*2^10*c.k,113678782763790+c.lower,113679171035175+c.upper)) = pointBounds58855 := by
 decide +kernel
def cuts58856 : List PrefixCut := [⟨64,209327316,209327433⟩]
theorem checked58856 : checkPrefixCuts (2^48) 7718305793 10 Manual.Count131072.C058856.packed 64 cuts58856 = true := by
 decide +kernel
def cuts58857 : List PrefixCut := [⟨24,77931576,77931619⟩,
⟨64,209032012,209032129⟩]
theorem checked58857 : checkPrefixCuts (2^48) 7718436865 10 Manual.Count131072.C058857.packed 64 cuts58857 = true := by
 decide +kernel
def pointBounds58857 : List (Nat × Nat × Nat) := [(7718486016,113679280702874,113679668974540)]
theorem point_links_checked58857 : (cuts58857.take 1).map (fun c => (7718436865-1+2*2^10*c.k,113679202771298+c.lower,113679591042921+c.upper)) = pointBounds58857 := by
 decide +kernel
def cuts58858 : List PrefixCut := [⟨64,208043866,208043979⟩]
theorem checked58858 : checkPrefixCuts (2^48) 7718567937 10 Manual.Count131072.C058858.packed 64 cuts58858 = true := by
 decide +kernel
def cuts58859 : List PrefixCut := [⟨14,46385462,46385489⟩,
⟨64,207566283,207566404⟩]
theorem checked58859 : checkPrefixCuts (2^48) 7718699009 10 Manual.Count131072.C058859.packed 64 cuts58859 = true := by
 decide +kernel
def pointBounds58859 : List (Nat × Nat × Nat) := [(7718727680,113679666232638,113680054504518)]
theorem point_links_checked58859 : (cuts58859.take 1).map (fun c => (7718699009-1+2*2^10*c.k,113679619847176+c.lower,113680008119029+c.upper)) = pointBounds58859 := by
 decide +kernel
def cuts58860 : List PrefixCut := [⟨64,210261205,210261323⟩]
theorem checked58860 : checkPrefixCuts (2^48) 7718830081 10 Manual.Count131072.C058860.packed 64 cuts58860 = true := by
 decide +kernel
def cuts58861 : List PrefixCut := [⟨4,13966235,13966242⟩,
⟨64,215545068,215545192⟩]
theorem checked58861 : checkPrefixCuts (2^48) 7718961153 10 Manual.Count131072.C058861.packed 64 cuts58861 = true := by
 decide +kernel
def pointBounds58861 : List (Nat × Nat × Nat) := [(7718969344,113680051640899,113680439912998)]
theorem point_links_checked58861 : (cuts58861.take 1).map (fun c => (7718961153-1+2*2^10*c.k,113680037674664+c.lower,113680425946756+c.upper)) = pointBounds58861 := by
 decide +kernel
def cuts58862 : List PrefixCut := [⟨58,190308159,190308267⟩,
⟨64,209707100,209707220⟩]
theorem checked58862 : checkPrefixCuts (2^48) 7719092225 10 Manual.Count131072.C058862.packed 64 cuts58862 = true := by
 decide +kernel
def pointBounds58862 : List (Nat × Nat × Nat) := [(7719211008,113680443527891,113680831800215)]
theorem point_links_checked58862 : (cuts58862.take 1).map (fun c => (7719092225-1+2*2^10*c.k,113680253219732+c.lower,113680641491948+c.upper)) = pointBounds58862 := by
 decide +kernel
def cuts58863 : List PrefixCut := [⟨64,209849377,209849495⟩]
theorem checked58863 : checkPrefixCuts (2^48) 7719223297 10 Manual.Count131072.C058863.packed 64 cuts58863 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000276
