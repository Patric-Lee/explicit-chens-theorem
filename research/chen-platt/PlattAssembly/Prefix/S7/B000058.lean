import PlattAssemblyKernel
import PlattCertificates.Count131072.C061856
import PlattCertificates.Count131072.C061857
import PlattCertificates.Count131072.C061858
import PlattCertificates.Count131072.C061859
import PlattCertificates.Count131072.C061860
import PlattCertificates.Count131072.C061861
import PlattCertificates.Count131072.C061862
import PlattCertificates.Count131072.C061863
import PlattCertificates.Count131072.C061864
import PlattCertificates.Count131072.C061865
import PlattCertificates.Count131072.C061866
import PlattCertificates.Count131072.C061867
import PlattCertificates.Count131072.C061868
import PlattCertificates.Count131072.C061869
import PlattCertificates.Count131072.C061870
import PlattCertificates.Count131072.C061871
import PlattCertificates.Count131072.C061872
import PlattCertificates.Count131072.C061873
import PlattCertificates.Count131072.C061874
import PlattCertificates.Count131072.C061875
import PlattCertificates.Count131072.C061876
import PlattCertificates.Count131072.C061877
import PlattCertificates.Count131072.C061878
import PlattCertificates.Count131072.C061879
import PlattCertificates.Count131072.C061880
import PlattCertificates.Count131072.C061881
import PlattCertificates.Count131072.C061882
import PlattCertificates.Count131072.C061883
import PlattCertificates.Count131072.C061884
import PlattCertificates.Count131072.C061885
import PlattCertificates.Count131072.C061886
import PlattCertificates.Count131072.C061887
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000058
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61856 : List PrefixCut := [⟨20,62599776,62599808⟩,
⟨64,199700496,199700607⟩]
theorem checked61856 : checkPrefixCuts (2^48) 8111521793 10 Manual.Count131072.C061856.packed 64 cuts61856 = true := by
 decide +kernel
def pointBounds61856 : List (Nat × Nat × Nat) := [(8111562752,114292792771260,114293181393612)]
theorem point_links_checked61856 : (cuts61856.take 1).map (fun c => (8111521793-1+2*2^10*c.k,114292730171484+c.lower,114293118793804+c.upper)) = pointBounds61856 := by
 decide +kernel
def cuts61857 : List PrefixCut := [⟨64,195533293,195533410⟩]
theorem checked61857 : checkPrefixCuts (2^48) 8111652865 10 Manual.Count131072.C061857.packed 64 cuts61857 = true := by
 decide +kernel
def cuts61858 : List PrefixCut := [⟨16,49724291,49724319⟩,
⟨64,199208263,199208368⟩]
theorem checked61858 : checkPrefixCuts (2^48) 8111783937 10 Manual.Count131072.C061858.packed 64 cuts61858 = true := by
 decide +kernel
def pointBounds61858 : List (Nat × Nat × Nat) := [(8111816704,114293175129564,114293563752140)]
theorem point_links_checked61858 : (cuts61858.take 1).map (fun c => (8111783937-1+2*2^10*c.k,114293125405273+c.lower,114293514027821+c.upper)) = pointBounds61858 := by
 decide +kernel
def cuts61859 : List PrefixCut := [⟨64,200072501,200072617⟩]
theorem checked61859 : checkPrefixCuts (2^48) 8111915009 10 Manual.Count131072.C061859.packed 64 cuts61859 = true := by
 decide +kernel
def cuts61860 : List PrefixCut := [⟨12,36849629,36849651⟩,
⟨64,199756990,199757109⟩]
theorem checked61860 : checkPrefixCuts (2^48) 8112046081 10 Manual.Count131072.C061860.packed 64 cuts61860 = true := by
 decide +kernel
def pointBounds61860 : List (Nat × Nat × Nat) := [(8112070656,114293561535666,114293950158457)]
theorem point_links_checked61860 : (cuts61860.take 1).map (fun c => (8112046081-1+2*2^10*c.k,114293524686037+c.lower,114293913308806+c.upper)) = pointBounds61860 := by
 decide +kernel
def cuts61861 : List PrefixCut := [⟨64,199545589,199545702⟩]
theorem checked61861 : checkPrefixCuts (2^48) 8112177153 10 Manual.Count131072.C061861.packed 64 cuts61861 = true := by
 decide +kernel
def cuts61862 : List PrefixCut := [⟨8,25502463,25502479⟩,
⟨64,197668712,197668831⟩]
theorem checked61862 : checkPrefixCuts (2^48) 8112308225 10 Manual.Count131072.C061862.packed 64 cuts61862 = true := by
 decide +kernel
def pointBounds61862 : List (Nat × Nat × Nat) := [(8112324608,114293949491079,114294338114096)]
theorem point_links_checked61862 : (cuts61862.take 1).map (fun c => (8112308225-1+2*2^10*c.k,114293923988616+c.lower,114294312611617+c.upper)) = pointBounds61862 := by
 decide +kernel
def cuts61863 : List PrefixCut := [⟨64,199088069,199088189⟩]
theorem checked61863 : checkPrefixCuts (2^48) 8112439297 10 Manual.Count131072.C061863.packed 64 cuts61863 = true := by
 decide +kernel
def cuts61864 : List PrefixCut := [⟨4,12178339,12178346⟩,
⟨64,197419450,197419565⟩]
theorem checked61864 : checkPrefixCuts (2^48) 8112570369 10 Manual.Count131072.C061864.packed 64 cuts61864 = true := by
 decide +kernel
def pointBounds61864 : List (Nat × Nat × Nat) := [(8112578560,114294332923736,114294721546983)]
theorem point_links_checked61864 : (cuts61864.take 1).map (fun c => (8112570369-1+2*2^10*c.k,114294320745397+c.lower,114294709368637+c.upper)) = pointBounds61864 := by
 decide +kernel
def cuts61865 : List PrefixCut := [⟨64,200434743,200434856⟩]
theorem checked61865 : checkPrefixCuts (2^48) 8112701441 10 Manual.Count131072.C061865.packed 64 cuts61865 = true := by
 decide +kernel
def pointBounds61865 : List (Nat × Nat × Nat) := [(8112832512,114294718599590,114295107223058)]
theorem point_links_checked61865 : (cuts61865.take 1).map (fun c => (8112701441-1+2*2^10*c.k,114294518164847+c.lower,114294906788202+c.upper)) = pointBounds61865 := by
 decide +kernel
def cuts61866 : List PrefixCut := [⟨64,196857958,196858076⟩]
theorem checked61866 : checkPrefixCuts (2^48) 8112832513 10 Manual.Count131072.C061866.packed 64 cuts61866 = true := by
 decide +kernel
def cuts61867 : List PrefixCut := [⟨60,187001727,187001832⟩,
⟨64,199109904,199110017⟩]
theorem checked61867 : checkPrefixCuts (2^48) 8112963585 10 Manual.Count131072.C061867.packed 64 cuts61867 = true := by
 decide +kernel
def pointBounds61867 : List (Nat × Nat × Nat) := [(8113086464,114295102459275,114295491082966)]
theorem point_links_checked61867 : (cuts61867.take 1).map (fun c => (8112963585-1+2*2^10*c.k,114294915457548+c.lower,114295304081134+c.upper)) = pointBounds61867 := by
 decide +kernel
def cuts61868 : List PrefixCut := [⟨64,197961788,197961904⟩]
theorem checked61868 : checkPrefixCuts (2^48) 8113094657 10 Manual.Count131072.C061868.packed 64 cuts61868 = true := by
 decide +kernel
def cuts61869 : List PrefixCut := [⟨56,175581747,175581846⟩,
⟨64,200248337,200248450⟩]
theorem checked61869 : checkPrefixCuts (2^48) 8113225729 10 Manual.Count131072.C061869.packed 64 cuts61869 = true := by
 decide +kernel
def pointBounds61869 : List (Nat × Nat × Nat) := [(8113340416,114295488110987,114295876734901)]
theorem point_links_checked61869 : (cuts61869.take 1).map (fun c => (8113225729-1+2*2^10*c.k,114295312529240+c.lower,114295701153055+c.upper)) = pointBounds61869 := by
 decide +kernel
def cuts61870 : List PrefixCut := [⟨64,201181798,201181918⟩]
theorem checked61870 : checkPrefixCuts (2^48) 8113356801 10 Manual.Count131072.C061870.packed 64 cuts61870 = true := by
 decide +kernel
def cuts61871 : List PrefixCut := [⟨52,161525921,161526008⟩,
⟨64,199097044,199097151⟩]
theorem checked61871 : checkPrefixCuts (2^48) 8113487873 10 Manual.Count131072.C061871.packed 64 cuts61871 = true := by
 decide +kernel
def pointBounds61871 : List (Nat × Nat × Nat) := [(8113594368,114295875485296,114296264109431)]
theorem point_links_checked61871 : (cuts61871.take 1).map (fun c => (8113487873-1+2*2^10*c.k,114295713959375+c.lower,114296102583423+c.upper)) = pointBounds61871 := by
 decide +kernel
def cuts61872 : List PrefixCut := [⟨64,199197899,199198013⟩]
theorem checked61872 : checkPrefixCuts (2^48) 8113618945 10 Manual.Count131072.C061872.packed 64 cuts61872 = true := by
 decide +kernel
def cuts61873 : List PrefixCut := [⟨48,150246222,150246306⟩,
⟨64,198743690,198743803⟩]
theorem checked61873 : checkPrefixCuts (2^48) 8113750017 10 Manual.Count131072.C061873.packed 64 cuts61873 = true := by
 decide +kernel
def pointBounds61873 : List (Nat × Nat × Nat) := [(8113848320,114296262500540,114296651124893)]
theorem point_links_checked61873 : (cuts61873.take 1).map (fun c => (8113750017-1+2*2^10*c.k,114296112254318+c.lower,114296500878587+c.upper)) = pointBounds61873 := by
 decide +kernel
def cuts61874 : List PrefixCut := [⟨64,199607759,199607876⟩]
theorem checked61874 : checkPrefixCuts (2^48) 8113881089 10 Manual.Count131072.C061874.packed 64 cuts61874 = true := by
 decide +kernel
def cuts61875 : List PrefixCut := [⟨44,138655071,138655147⟩,
⟨64,200020801,200020915⟩]
theorem checked61875 : checkPrefixCuts (2^48) 8114012161 10 Manual.Count131072.C061875.packed 64 cuts61875 = true := by
 decide +kernel
def pointBounds61875 : List (Nat × Nat × Nat) := [(8114102272,114296649260838,114297037885413)]
theorem point_links_checked61875 : (cuts61875.take 1).map (fun c => (8114012161-1+2*2^10*c.k,114296510605767+c.lower,114296899230266+c.upper)) = pointBounds61875 := by
 decide +kernel
def cuts61876 : List PrefixCut := [⟨64,201058238,201058352⟩]
theorem checked61876 : checkPrefixCuts (2^48) 8114143233 10 Manual.Count131072.C061876.packed 64 cuts61876 = true := by
 decide +kernel
def cuts61877 : List PrefixCut := [⟨40,122763242,122763314⟩,
⟨64,193943841,193943955⟩]
theorem checked61877 : checkPrefixCuts (2^48) 8114274305 10 Manual.Count131072.C061877.packed 64 cuts61877 = true := by
 decide +kernel
def pointBounds61877 : List (Nat × Nat × Nat) := [(8114356224,114297034448048,114297423072847)]
theorem point_links_checked61877 : (cuts61877.take 1).map (fun c => (8114274305-1+2*2^10*c.k,114296911684806+c.lower,114297300309533+c.upper)) = pointBounds61877 := by
 decide +kernel
def cuts61878 : List PrefixCut := [⟨64,197964508,197964620⟩]
theorem checked61878 : checkPrefixCuts (2^48) 8114405377 10 Manual.Count131072.C061878.packed 64 cuts61878 = true := by
 decide +kernel
def cuts61879 : List PrefixCut := [⟨36,115058692,115058759⟩,
⟨64,201048503,201048621⟩]
theorem checked61879 : checkPrefixCuts (2^48) 8114536449 10 Manual.Count131072.C061879.packed 64 cuts61879 = true := by
 decide +kernel
def pointBounds61879 : List (Nat × Nat × Nat) := [(8114610176,114297418651847,114297807276867)]
theorem point_links_checked61879 : (cuts61879.take 1).map (fun c => (8114536449-1+2*2^10*c.k,114297303593155+c.lower,114297692218108+c.upper)) = pointBounds61879 := by
 decide +kernel
def cuts61880 : List PrefixCut := [⟨64,199761836,199761955⟩]
theorem checked61880 : checkPrefixCuts (2^48) 8114667521 10 Manual.Count131072.C061880.packed 64 cuts61880 = true := by
 decide +kernel
def cuts61881 : List PrefixCut := [⟨32,100139853,100139912⟩,
⟨64,201770406,201770522⟩]
theorem checked61881 : checkPrefixCuts (2^48) 8114798593 10 Manual.Count131072.C061881.packed 64 cuts61881 = true := by
 decide +kernel
def pointBounds61881 : List (Nat × Nat × Nat) := [(8114864128,114297804543347,114298193168596)]
theorem point_links_checked61881 : (cuts61881.take 1).map (fun c => (8114798593-1+2*2^10*c.k,114297704403494+c.lower,114298093028684+c.upper)) = pointBounds61881 := by
 decide +kernel
def cuts61882 : List PrefixCut := [⟨64,200691881,200691999⟩]
theorem checked61882 : checkPrefixCuts (2^48) 8114929665 10 Manual.Count131072.C061882.packed 64 cuts61882 = true := by
 decide +kernel
def cuts61883 : List PrefixCut := [⟨28,86644058,86644106⟩,
⟨64,200931429,200931544⟩]
theorem checked61883 : checkPrefixCuts (2^48) 8115060737 10 Manual.Count131072.C061883.packed 64 cuts61883 = true := by
 decide +kernel
def pointBounds61883 : List (Nat × Nat × Nat) := [(8115118080,114298193509839,114298582135311)]
theorem point_links_checked61883 : (cuts61883.take 1).map (fun c => (8115060737-1+2*2^10*c.k,114298106865781+c.lower,114298495491205+c.upper)) = pointBounds61883 := by
 decide +kernel
def cuts61884 : List PrefixCut := [⟨64,197251634,197251746⟩]
theorem checked61884 : checkPrefixCuts (2^48) 8115191809 10 Manual.Count131072.C061884.packed 64 cuts61884 = true := by
 decide +kernel
def cuts61885 : List PrefixCut := [⟨24,73808126,73808169⟩,
⟨64,196589446,196589558⟩]
theorem checked61885 : checkPrefixCuts (2^48) 8115322881 10 Manual.Count131072.C061885.packed 64 cuts61885 = true := by
 decide +kernel
def pointBounds61885 : List (Nat × Nat × Nat) := [(8115372032,114298578856970,114298967482664)]
theorem point_links_checked61885 : (cuts61885.take 1).map (fun c => (8115322881-1+2*2^10*c.k,114298505048844+c.lower,114298893674495+c.upper)) = pointBounds61885 := by
 decide +kernel
def cuts61886 : List PrefixCut := [⟨64,200054626,200054740⟩]
theorem checked61886 : checkPrefixCuts (2^48) 8115453953 10 Manual.Count131072.C061886.packed 64 cuts61886 = true := by
 decide +kernel
def cuts61887 : List PrefixCut := [⟨20,61944135,61944169⟩,
⟨64,198247866,198247978⟩]
theorem checked61887 : checkPrefixCuts (2^48) 8115585025 10 Manual.Count131072.C061887.packed 64 cuts61887 = true := by
 decide +kernel
def pointBounds61887 : List (Nat × Nat × Nat) := [(8115625984,114298963637051,114299352262962)]
theorem point_links_checked61887 : (cuts61887.take 1).map (fun c => (8115585025-1+2*2^10*c.k,114298901692916+c.lower,114299290318793+c.upper)) = pointBounds61887 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000058
