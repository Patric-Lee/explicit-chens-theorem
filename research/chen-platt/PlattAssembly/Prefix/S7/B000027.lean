import PlattAssemblyKernel
import PlattCertificates.Count131072.C060864
import PlattCertificates.Count131072.C060865
import PlattCertificates.Count131072.C060866
import PlattCertificates.Count131072.C060867
import PlattCertificates.Count131072.C060868
import PlattCertificates.Count131072.C060869
import PlattCertificates.Count131072.C060870
import PlattCertificates.Count131072.C060871
import PlattCertificates.Count131072.C060872
import PlattCertificates.Count131072.C060873
import PlattCertificates.Count131072.C060874
import PlattCertificates.Count131072.C060875
import PlattCertificates.Count131072.C060876
import PlattCertificates.Count131072.C060877
import PlattCertificates.Count131072.C060878
import PlattCertificates.Count131072.C060879
import PlattCertificates.Count131072.C060880
import PlattCertificates.Count131072.C060881
import PlattCertificates.Count131072.C060882
import PlattCertificates.Count131072.C060883
import PlattCertificates.Count131072.C060884
import PlattCertificates.Count131072.C060885
import PlattCertificates.Count131072.C060886
import PlattCertificates.Count131072.C060887
import PlattCertificates.Count131072.C060888
import PlattCertificates.Count131072.C060889
import PlattCertificates.Count131072.C060890
import PlattCertificates.Count131072.C060891
import PlattCertificates.Count131072.C060892
import PlattCertificates.Count131072.C060893
import PlattCertificates.Count131072.C060894
import PlattCertificates.Count131072.C060895
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000027
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60864 : List PrefixCut := [⟨20,62244192,62244227⟩,
⟨64,200308783,200308898⟩]
theorem checked60864 : checkPrefixCuts (2^48) 7981498369 10 Manual.Count131072.C060864.packed 64 cuts60864 = true := by
 decide +kernel
def pointBounds60864 : List (Nat × Nat × Nat) := [(7981539328,114093348502894,114093737011022)]
theorem point_links_checked60864 : (cuts60864.take 1).map (fun c => (7981498369-1+2*2^10*c.k,114093286258702+c.lower,114093674766795+c.upper)) = pointBounds60864 := by
 decide +kernel
def cuts60865 : List PrefixCut := [⟨64,202033472,202033586⟩]
theorem checked60865 : checkPrefixCuts (2^48) 7981629441 10 Manual.Count131072.C060865.packed 64 cuts60865 = true := by
 decide +kernel
def cuts60866 : List PrefixCut := [⟨14,45420933,45420960⟩,
⟨64,205168709,205168830⟩]
theorem checked60866 : checkPrefixCuts (2^48) 7981760513 10 Manual.Count131072.C060866.packed 64 cuts60866 = true := by
 decide +kernel
def pointBounds60866 : List (Nat × Nat × Nat) := [(7981789184,114093734021890,114094122530239)]
theorem point_links_checked60866 : (cuts60866.take 1).map (fun c => (7981760513-1+2*2^10*c.k,114093688600957+c.lower,114094077109279+c.upper)) = pointBounds60866 := by
 decide +kernel
def cuts60867 : List PrefixCut := [⟨64,201991585,201991699⟩]
theorem checked60867 : checkPrefixCuts (2^48) 7981891585 10 Manual.Count131072.C060867.packed 64 cuts60867 = true := by
 decide +kernel
def cuts60868 : List PrefixCut := [⟨8,24755025,24755039⟩,
⟨64,200895102,200895215⟩]
theorem checked60868 : checkPrefixCuts (2^48) 7982022657 10 Manual.Count131072.C060868.packed 64 cuts60868 = true := by
 decide +kernel
def pointBounds60868 : List (Nat × Nat × Nat) := [(7982039040,114094120516276,114094509024847)]
theorem point_links_checked60868 : (cuts60868.take 1).map (fun c => (7982022657-1+2*2^10*c.k,114094095761251+c.lower,114094484269808+c.upper)) = pointBounds60868 := by
 decide +kernel
def cuts60869 : List PrefixCut := [⟨64,201138663,201138774⟩]
theorem checked60869 : checkPrefixCuts (2^48) 7982153729 10 Manual.Count131072.C060869.packed 64 cuts60869 = true := by
 decide +kernel
def cuts60870 : List PrefixCut := [⟨2,6911438,6911442⟩,
⟨64,202933723,202933838⟩]
theorem checked60870 : checkPrefixCuts (2^48) 7982284801 10 Manual.Count131072.C060870.packed 64 cuts60870 = true := by
 decide +kernel
def pointBounds60870 : List (Nat × Nat × Nat) := [(7982288896,114094504706454,114094893215239)]
theorem point_links_checked60870 : (cuts60870.take 1).map (fun c => (7982284801-1+2*2^10*c.k,114094497795016+c.lower,114094886303797+c.upper)) = pointBounds60870 := by
 decide +kernel
def cuts60871 : List PrefixCut := [⟨60,190447886,190447997⟩,
⟨64,203459308,203459427⟩]
theorem checked60871 : checkPrefixCuts (2^48) 7982415873 10 Manual.Count131072.C060871.packed 64 cuts60871 = true := by
 decide +kernel
def pointBounds60871 : List (Nat × Nat × Nat) := [(7982538752,114094891176625,114095279685632)]
theorem point_links_checked60871 : (cuts60871.take 1).map (fun c => (7982415873-1+2*2^10*c.k,114094700728739+c.lower,114095089237635+c.upper)) = pointBounds60871 := by
 decide +kernel
def cuts60872 : List PrefixCut := [⟨64,204901663,204901787⟩]
theorem checked60872 : checkPrefixCuts (2^48) 7982546945 10 Manual.Count131072.C060872.packed 64 cuts60872 = true := by
 decide +kernel
def cuts60873 : List PrefixCut := [⟨54,173798843,173798936⟩,
⟨64,205956125,205956237⟩]
theorem checked60873 : checkPrefixCuts (2^48) 7982678017 10 Manual.Count131072.C060873.packed 64 cuts60873 = true := by
 decide +kernel
def pointBounds60873 : List (Nat × Nat × Nat) := [(7982788608,114095282888553,114095671397785)]
theorem point_links_checked60873 : (cuts60873.take 1).map (fun c => (7982678017-1+2*2^10*c.k,114095109089710+c.lower,114095497598849+c.upper)) = pointBounds60873 := by
 decide +kernel
def cuts60874 : List PrefixCut := [⟨64,200628489,200628606⟩]
theorem checked60874 : checkPrefixCuts (2^48) 7982809089 10 Manual.Count131072.C060874.packed 64 cuts60874 = true := by
 decide +kernel
def cuts60875 : List PrefixCut := [⟨48,152108765,152108853⟩,
⟨64,202670238,202670356⟩]
theorem checked60875 : checkPrefixCuts (2^48) 7982940161 10 Manual.Count131072.C060875.packed 64 cuts60875 = true := by
 decide +kernel
def pointBounds60875 : List (Nat × Nat × Nat) := [(7983038464,114095667783089,114096056292545)]
theorem point_links_checked60875 : (cuts60875.take 1).map (fun c => (7982940161-1+2*2^10*c.k,114095515674324+c.lower,114095904183692+c.upper)) = pointBounds60875 := by
 decide +kernel
def cuts60876 : List PrefixCut := [⟨64,202349596,202349713⟩]
theorem checked60876 : checkPrefixCuts (2^48) 7983071233 10 Manual.Count131072.C060876.packed 64 cuts60876 = true := by
 decide +kernel
def cuts60877 : List PrefixCut := [⟨42,132711886,132711962⟩,
⟨64,202593073,202593190⟩]
theorem checked60877 : checkPrefixCuts (2^48) 7983202305 10 Manual.Count131072.C060877.packed 64 cuts60877 = true := by
 decide +kernel
def pointBounds60877 : List (Nat × Nat × Nat) := [(7983288320,114096053406044,114096441915723)]
theorem point_links_checked60877 : (cuts60877.take 1).map (fun c => (7983202305-1+2*2^10*c.k,114095920694158+c.lower,114096309203761+c.upper)) = pointBounds60877 := by
 decide +kernel
def cuts60878 : List PrefixCut := [⟨64,200192239,200192354⟩]
theorem checked60878 : checkPrefixCuts (2^48) 7983333377 10 Manual.Count131072.C060878.packed 64 cuts60878 = true := by
 decide +kernel
def cuts60879 : List PrefixCut := [⟨36,114127147,114127216⟩,
⟨64,203467840,203467960⟩]
theorem checked60879 : checkPrefixCuts (2^48) 7983464449 10 Manual.Count131072.C060879.packed 64 cuts60879 = true := by
 decide +kernel
def pointBounds60879 : List (Nat × Nat × Nat) := [(7983538176,114096437606617,114096826116521)]
theorem point_links_checked60879 : (cuts60879.take 1).map (fun c => (7983464449-1+2*2^10*c.k,114096323479470+c.lower,114096711989305+c.upper)) = pointBounds60879 := by
 decide +kernel
def cuts60880 : List PrefixCut := [⟨64,201454890,201455006⟩]
theorem checked60880 : checkPrefixCuts (2^48) 7983595521 10 Manual.Count131072.C060880.packed 64 cuts60880 = true := by
 decide +kernel
def cuts60881 : List PrefixCut := [⟨30,94591695,94591752⟩,
⟨64,202297718,202297839⟩]
theorem checked60881 : checkPrefixCuts (2^48) 7983726593 10 Manual.Count131072.C060881.packed 64 cuts60881 = true := by
 decide +kernel
def pointBounds60881 : List (Nat × Nat × Nat) := [(7983788032,114096822993895,114097211504023)]
theorem point_links_checked60881 : (cuts60881.take 1).map (fun c => (7983726593-1+2*2^10*c.k,114096728402200+c.lower,114097116912271+c.upper)) = pointBounds60881 := by
 decide +kernel
def cuts60882 : List PrefixCut := [⟨64,202752722,202752839⟩]
theorem checked60882 : checkPrefixCuts (2^48) 7983857665 10 Manual.Count131072.C060882.packed 64 cuts60882 = true := by
 decide +kernel
def cuts60883 : List PrefixCut := [⟨24,76608707,76608752⟩,
⟨64,201057171,201057286⟩]
theorem checked60883 : checkPrefixCuts (2^48) 7983988737 10 Manual.Count131072.C060883.packed 64 cuts60883 = true := by
 decide +kernel
def pointBounds60883 : List (Nat × Nat × Nat) := [(7984037888,114097210061347,114097598571701)]
theorem point_links_checked60883 : (cuts60883.take 1).map (fun c => (7983988737-1+2*2^10*c.k,114097133452640+c.lower,114097521962949+c.upper)) = pointBounds60883 := by
 decide +kernel
def cuts60884 : List PrefixCut := [⟨64,202428766,202428880⟩]
theorem checked60884 : checkPrefixCuts (2^48) 7984119809 10 Manual.Count131072.C060884.packed 64 cuts60884 = true := by
 decide +kernel
def cuts60885 : List PrefixCut := [⟨18,56793682,56793715⟩,
⟨64,203659321,203659438⟩]
theorem checked60885 : checkPrefixCuts (2^48) 7984250881 10 Manual.Count131072.C060885.packed 64 cuts60885 = true := by
 decide +kernel
def pointBounds60885 : List (Nat × Nat × Nat) := [(7984287744,114097593732259,114097982242830)]
theorem point_links_checked60885 : (cuts60885.take 1).map (fun c => (7984250881-1+2*2^10*c.k,114097536938577+c.lower,114097925449115+c.upper)) = pointBounds60885 := by
 decide +kernel
def cuts60886 : List PrefixCut := [⟨64,201858082,201858197⟩]
theorem checked60886 : checkPrefixCuts (2^48) 7984381953 10 Manual.Count131072.C060886.packed 64 cuts60886 = true := by
 decide +kernel
def cuts60887 : List PrefixCut := [⟨12,37755483,37755504⟩,
⟨64,202101533,202101651⟩]
theorem checked60887 : checkPrefixCuts (2^48) 7984513025 10 Manual.Count131072.C060887.packed 64 cuts60887 = true := by
 decide +kernel
def pointBounds60887 : List (Nat × Nat × Nat) := [(7984537600,114097980211463,114098368722254)]
theorem point_links_checked60887 : (cuts60887.take 1).map (fun c => (7984513025-1+2*2^10*c.k,114097942455980+c.lower,114098330966750+c.upper)) = pointBounds60887 := by
 decide +kernel
def cuts60888 : List PrefixCut := [⟨64,204142818,204142936⟩]
theorem checked60888 : checkPrefixCuts (2^48) 7984644097 10 Manual.Count131072.C060888.packed 64 cuts60888 = true := by
 decide +kernel
def cuts60889 : List PrefixCut := [⟨6,18965266,18965276⟩,
⟨64,202588418,202588536⟩]
theorem checked60889 : checkPrefixCuts (2^48) 7984775169 10 Manual.Count131072.C060889.packed 64 cuts60889 = true := by
 decide +kernel
def pointBounds60889 : List (Nat × Nat × Nat) := [(7984787456,114098367665597,114098756176613)]
theorem point_links_checked60889 : (cuts60889.take 1).map (fun c => (7984775169-1+2*2^10*c.k,114098348700331+c.lower,114098737211337+c.upper)) = pointBounds60889 := by
 decide +kernel
def cuts60890 : List PrefixCut := [⟨64,199377301,199377414⟩]
theorem checked60890 : checkPrefixCuts (2^48) 7984906241 10 Manual.Count131072.C060890.packed 64 cuts60890 = true := by
 decide +kernel
def pointBounds60890 : List (Nat × Nat × Nat) := [(7985037312,114098750666050,114099139177287)]
theorem point_links_checked60890 : (cuts60890.take 1).map (fun c => (7984906241-1+2*2^10*c.k,114098551288749+c.lower,114098939799873+c.upper)) = pointBounds60890 := by
 decide +kernel
def cuts60891 : List PrefixCut := [⟨64,203674526,203674639⟩]
theorem checked60891 : checkPrefixCuts (2^48) 7985037313 10 Manual.Count131072.C060891.packed 64 cuts60891 = true := by
 decide +kernel
def cuts60892 : List PrefixCut := [⟨58,182415901,182416009⟩,
⟨64,202120183,202120301⟩]
theorem checked60892 : checkPrefixCuts (2^48) 7985168385 10 Manual.Count131072.C060892.packed 64 cuts60892 = true := by
 decide +kernel
def pointBounds60892 : List (Nat × Nat × Nat) := [(7985287168,114099136756477,114099525267935)]
theorem point_links_checked60892 : (cuts60892.take 1).map (fun c => (7985168385-1+2*2^10*c.k,114098954340576+c.lower,114099342851926+c.upper)) = pointBounds60892 := by
 decide +kernel
def cuts60893 : List PrefixCut := [⟨64,204443290,204443401⟩]
theorem checked60893 : checkPrefixCuts (2^48) 7985299457 10 Manual.Count131072.C060893.packed 64 cuts60893 = true := by
 decide +kernel
def cuts60894 : List PrefixCut := [⟨52,166090077,166090170⟩,
⟨64,204651423,204651538⟩]
theorem checked60894 : checkPrefixCuts (2^48) 7985430529 10 Manual.Count131072.C060894.packed 64 cuts60894 = true := by
 decide +kernel
def pointBounds60894 : List (Nat × Nat × Nat) := [(7985537024,114099526994126,114099915505798)]
theorem point_links_checked60894 : (cuts60894.take 1).map (fun c => (7985430529-1+2*2^10*c.k,114099360904049+c.lower,114099749415628+c.upper)) = pointBounds60894 := by
 decide +kernel
def cuts60895 : List PrefixCut := [⟨64,201828273,201828385⟩]
theorem checked60895 : checkPrefixCuts (2^48) 7985561601 10 Manual.Count131072.C060895.packed 64 cuts60895 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000027
