import PlattAssemblyKernel
import PlattCertificates.Count131072.C067872
import PlattCertificates.Count131072.C067873
import PlattCertificates.Count131072.C067874
import PlattCertificates.Count131072.C067875
import PlattCertificates.Count131072.C067876
import PlattCertificates.Count131072.C067877
import PlattCertificates.Count131072.C067878
import PlattCertificates.Count131072.C067879
import PlattCertificates.Count131072.C067880
import PlattCertificates.Count131072.C067881
import PlattCertificates.Count131072.C067882
import PlattCertificates.Count131072.C067883
import PlattCertificates.Count131072.C067884
import PlattCertificates.Count131072.C067885
import PlattCertificates.Count131072.C067886
import PlattCertificates.Count131072.C067887
import PlattCertificates.Count131072.C067888
import PlattCertificates.Count131072.C067889
import PlattCertificates.Count131072.C067890
import PlattCertificates.Count131072.C067891
import PlattCertificates.Count131072.C067892
import PlattCertificates.Count131072.C067893
import PlattCertificates.Count131072.C067894
import PlattCertificates.Count131072.C067895
import PlattCertificates.Count131072.C067896
import PlattCertificates.Count131072.C067897
import PlattCertificates.Count131072.C067898
import PlattCertificates.Count131072.C067899
import PlattCertificates.Count131072.C067900
import PlattCertificates.Count131072.C067901
import PlattCertificates.Count131072.C067902
import PlattCertificates.Count131072.C067903
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000246
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67872 : List PrefixCut := [⟨64,181564765,181564870⟩]
theorem checked67872 : checkPrefixCuts (2^48) 8900050945 10 Manual.Count131072.C067872.packed 64 cuts67872 = true := by
 decide +kernel
def cuts67873 : List PrefixCut := [⟨45,126502336,126502414⟩,
⟨64,181688572,181688681⟩]
theorem checked67873 : checkPrefixCuts (2^48) 8900182017 10 Manual.Count131072.C067873.packed 64 cuts67873 = true := by
 decide +kernel
def pointBounds67873 : List (Nat × Nat × Nat) := [(8900274176,115435182895779,115435572179001)]
theorem point_links_checked67873 : (cuts67873.take 1).map (fun c => (8900182017-1+2*2^10*c.k,115435056393443+c.lower,115435445676587+c.upper)) = pointBounds67873 := by
 decide +kernel
def cuts67874 : List PrefixCut := [⟨64,183172271,183172377⟩]
theorem checked67874 : checkPrefixCuts (2^48) 8900313089 10 Manual.Count131072.C067874.packed 64 cuts67874 = true := by
 decide +kernel
def cuts67875 : List PrefixCut := [⟨53,146959616,146959698⟩,
⟨64,178331012,178331112⟩]
theorem checked67875 : checkPrefixCuts (2^48) 8900444161 10 Manual.Count131072.C067875.packed 64 cuts67875 = true := by
 decide +kernel
def pointBounds67875 : List (Nat × Nat × Nat) := [(8900552704,115435568213902,115435957497343)]
theorem point_links_checked67875 : (cuts67875.take 1).map (fun c => (8900444161-1+2*2^10*c.k,115435421254286+c.lower,115435810537645+c.upper)) = pointBounds67875 := by
 decide +kernel
def cuts67876 : List PrefixCut := [⟨64,180447199,180447309⟩]
theorem checked67876 : checkPrefixCuts (2^48) 8900575233 10 Manual.Count131072.C067876.packed 64 cuts67876 = true := by
 decide +kernel
def cuts67877 : List PrefixCut := [⟨61,172032715,172032815⟩,
⟨64,180476170,180476276⟩]
theorem checked67877 : checkPrefixCuts (2^48) 8900706305 10 Manual.Count131072.C067877.packed 64 cuts67877 = true := by
 decide +kernel
def pointBounds67877 : List (Nat × Nat × Nat) := [(8900831232,115435952065212,115436341348881)]
theorem point_links_checked67877 : (cuts67877.take 1).map (fun c => (8900706305-1+2*2^10*c.k,115435780032497+c.lower,115436169316066+c.upper)) = pointBounds67877 := by
 decide +kernel
def cuts67878 : List PrefixCut := [⟨64,181042725,181042832⟩]
theorem checked67878 : checkPrefixCuts (2^48) 8900837377 10 Manual.Count131072.C067878.packed 64 cuts67878 = true := by
 decide +kernel
def cuts67879 : List PrefixCut := [⟨64,176992357,176992462⟩]
theorem checked67879 : checkPrefixCuts (2^48) 8900968449 10 Manual.Count131072.C067879.packed 64 cuts67879 = true := by
 decide +kernel
def cuts67880 : List PrefixCut := [⟨5,14230110,14230118⟩,
⟨64,181163882,181163980⟩]
theorem checked67880 : checkPrefixCuts (2^48) 8901099521 10 Manual.Count131072.C067880.packed 64 cuts67880 = true := by
 decide +kernel
def pointBounds67880 : List (Nat × Nat × Nat) := [(8901109760,115436332773859,115436722057754)]
theorem point_links_checked67880 : (cuts67880.take 1).map (fun c => (8901099521-1+2*2^10*c.k,115436318543749+c.lower,115436707827636+c.upper)) = pointBounds67880 := by
 decide +kernel
def cuts67881 : List PrefixCut := [⟨64,181477443,181477548⟩]
theorem checked67881 : checkPrefixCuts (2^48) 8901230593 10 Manual.Count131072.C067881.packed 64 cuts67881 = true := by
 decide +kernel
def cuts67882 : List PrefixCut := [⟨13,36554462,36554484⟩,
⟨64,180336396,180336498⟩]
theorem checked67882 : checkPrefixCuts (2^48) 8901361665 10 Manual.Count131072.C067882.packed 64 cuts67882 = true := by
 decide +kernel
def pointBounds67882 : List (Nat × Nat × Nat) := [(8901388288,115436717739536,115437107023648)]
theorem point_links_checked67882 : (cuts67882.take 1).map (fun c => (8901361665-1+2*2^10*c.k,115436681185074+c.lower,115437070469164+c.upper)) = pointBounds67882 := by
 decide +kernel
def cuts67883 : List PrefixCut := [⟨64,181219126,181219235⟩]
theorem checked67883 : checkPrefixCuts (2^48) 8901492737 10 Manual.Count131072.C067883.packed 64 cuts67883 = true := by
 decide +kernel
def cuts67884 : List PrefixCut := [⟨21,57517773,57517811⟩,
⟨64,178971406,178971513⟩]
theorem checked67884 : checkPrefixCuts (2^48) 8901623809 10 Manual.Count131072.C067884.packed 64 cuts67884 = true := by
 decide +kernel
def pointBounds67884 : List (Nat × Nat × Nat) := [(8901666816,115437100258369,115437489542708)]
theorem point_links_checked67884 : (cuts67884.take 1).map (fun c => (8901623809-1+2*2^10*c.k,115437042740596+c.lower,115437432024897+c.upper)) = pointBounds67884 := by
 decide +kernel
def cuts67885 : List PrefixCut := [⟨64,180865974,180866079⟩]
theorem checked67885 : checkPrefixCuts (2^48) 8901754881 10 Manual.Count131072.C067885.packed 64 cuts67885 = true := by
 decide +kernel
def cuts67886 : List PrefixCut := [⟨29,82685220,82685269⟩,
⟨64,180831694,180831804⟩]
theorem checked67886 : checkPrefixCuts (2^48) 8901885953 10 Manual.Count131072.C067886.packed 64 cuts67886 = true := by
 decide +kernel
def pointBounds67886 : List (Nat × Nat × Nat) := [(8901945344,115437485263196,115437874547758)]
theorem point_links_checked67886 : (cuts67886.take 1).map (fun c => (8901885953-1+2*2^10*c.k,115437402577976+c.lower,115437791862489+c.upper)) = pointBounds67886 := by
 decide +kernel
def cuts67887 : List PrefixCut := [⟨64,180765789,180765895⟩]
theorem checked67887 : checkPrefixCuts (2^48) 8902017025 10 Manual.Count131072.C067887.packed 64 cuts67887 = true := by
 decide +kernel
def cuts67888 : List PrefixCut := [⟨37,105859162,105859220⟩,
⟨64,181838163,181838265⟩]
theorem checked67888 : checkPrefixCuts (2^48) 8902148097 10 Manual.Count131072.C067888.packed 64 cuts67888 = true := by
 decide +kernel
def pointBounds67888 : List (Nat × Nat × Nat) := [(8902223872,115437870034621,115438259319408)]
theorem point_links_checked67888 : (cuts67888.take 1).map (fun c => (8902148097-1+2*2^10*c.k,115437764175459+c.lower,115438153460188+c.upper)) = pointBounds67888 := by
 decide +kernel
def cuts67889 : List PrefixCut := [⟨64,180539141,180539243⟩]
theorem checked67889 : checkPrefixCuts (2^48) 8902279169 10 Manual.Count131072.C067889.packed 64 cuts67889 = true := by
 decide +kernel
def cuts67890 : List PrefixCut := [⟨45,125775071,125775147⟩,
⟨64,179682796,179682902⟩]
theorem checked67890 : checkPrefixCuts (2^48) 8902410241 10 Manual.Count131072.C067890.packed 64 cuts67890 = true := by
 decide +kernel
def pointBounds67890 : List (Nat × Nat × Nat) := [(8902502400,115438252327834,115438641612843)]
theorem point_links_checked67890 : (cuts67890.take 1).map (fun c => (8902410241-1+2*2^10*c.k,115438126552763+c.lower,115438515837696+c.upper)) = pointBounds67890 := by
 decide +kernel
def cuts67891 : List PrefixCut := [⟨64,181672037,181672148⟩]
theorem checked67891 : checkPrefixCuts (2^48) 8902541313 10 Manual.Count131072.C067891.packed 64 cuts67891 = true := by
 decide +kernel
def cuts67892 : List PrefixCut := [⟨53,149863190,149863278⟩,
⟨64,181289964,181290071⟩]
theorem checked67892 : checkPrefixCuts (2^48) 8902672385 10 Manual.Count131072.C067892.packed 64 cuts67892 = true := by
 decide +kernel
def pointBounds67892 : List (Nat × Nat × Nat) := [(8902780928,115438637770786,115439027056024)]
theorem point_links_checked67892 : (cuts67892.take 1).map (fun c => (8902672385-1+2*2^10*c.k,115438487907596+c.lower,115438877192746+c.upper)) = pointBounds67892 := by
 decide +kernel
def cuts67893 : List PrefixCut := [⟨64,179991036,179991139⟩]
theorem checked67893 : checkPrefixCuts (2^48) 8902803457 10 Manual.Count131072.C067893.packed 64 cuts67893 = true := by
 decide +kernel
def cuts67894 : List PrefixCut := [⟨61,171673504,171673604⟩,
⟨64,180525847,180525953⟩]
theorem checked67894 : checkPrefixCuts (2^48) 8902934529 10 Manual.Count131072.C067894.packed 64 cuts67894 = true := by
 decide +kernel
def pointBounds67894 : List (Nat × Nat × Nat) := [(8903059456,115439020862100,115439410147560)]
theorem point_links_checked67894 : (cuts67894.take 1).map (fun c => (8902934529-1+2*2^10*c.k,115438849188596+c.lower,115439238473956+c.upper)) = pointBounds67894 := by
 decide +kernel
def cuts67895 : List PrefixCut := [⟨64,182641423,182641528⟩]
theorem checked67895 : checkPrefixCuts (2^48) 8903065601 10 Manual.Count131072.C067895.packed 64 cuts67895 = true := by
 decide +kernel
def cuts67896 : List PrefixCut := [⟨64,178750108,178750207⟩]
theorem checked67896 : checkPrefixCuts (2^48) 8903196673 10 Manual.Count131072.C067896.packed 64 cuts67896 = true := by
 decide +kernel
def cuts67897 : List PrefixCut := [⟨5,13341342,13341349⟩,
⟨64,180359794,180359906⟩]
theorem checked67897 : checkPrefixCuts (2^48) 8903327745 10 Manual.Count131072.C067897.packed 64 cuts67897 = true := by
 decide +kernel
def pointBounds67897 : List (Nat × Nat × Nat) := [(8903337984,115439404447316,115439793732993)]
theorem point_links_checked67897 : (cuts67897.take 1).map (fun c => (8903327745-1+2*2^10*c.k,115439391105974+c.lower,115439780391644+c.upper)) = pointBounds67897 := by
 decide +kernel
def cuts67898 : List PrefixCut := [⟨64,181874621,181874726⟩]
theorem checked67898 : checkPrefixCuts (2^48) 8903458817 10 Manual.Count131072.C067898.packed 64 cuts67898 = true := by
 decide +kernel
def cuts67899 : List PrefixCut := [⟨13,36102722,36102745⟩,
⟨64,180449328,180449431⟩]
theorem checked67899 : checkPrefixCuts (2^48) 8903589889 10 Manual.Count131072.C067899.packed 64 cuts67899 = true := by
 decide +kernel
def pointBounds67899 : List (Nat × Nat × Nat) := [(8903616512,115439789443111,115440178729021)]
theorem point_links_checked67899 : (cuts67899.take 1).map (fun c => (8903589889-1+2*2^10*c.k,115439753340389+c.lower,115440142626276+c.upper)) = pointBounds67899 := by
 decide +kernel
def cuts67900 : List PrefixCut := [⟨64,180478289,180478406⟩]
theorem checked67900 : checkPrefixCuts (2^48) 8903720961 10 Manual.Count131072.C067900.packed 64 cuts67900 = true := by
 decide +kernel
def cuts67901 : List PrefixCut := [⟨21,58356927,58356959⟩,
⟨64,180475632,180475732⟩]
theorem checked67901 : checkPrefixCuts (2^48) 8903852033 10 Manual.Count131072.C067901.packed 64 cuts67901 = true := by
 decide +kernel
def pointBounds67901 : List (Nat × Nat × Nat) := [(8903895040,115440172624933,115440561911072)]
theorem point_links_checked67901 : (cuts67901.take 1).map (fun c => (8903852033-1+2*2^10*c.k,115440114268006+c.lower,115440503554113+c.upper)) = pointBounds67901 := by
 decide +kernel
def cuts67902 : List PrefixCut := [⟨64,182464534,182464642⟩]
theorem checked67902 : checkPrefixCuts (2^48) 8903983105 10 Manual.Count131072.C067902.packed 64 cuts67902 = true := by
 decide +kernel
def cuts67903 : List PrefixCut := [⟨29,80641380,80641427⟩,
⟨64,175728592,175728701⟩]
theorem checked67903 : checkPrefixCuts (2^48) 8904114177 10 Manual.Count131072.C067903.packed 64 cuts67903 = true := by
 decide +kernel
def pointBounds67903 : List (Nat × Nat × Nat) := [(8904173568,115440557849552,115440947135914)]
theorem point_links_checked67903 : (cuts67903.take 1).map (fun c => (8904114177-1+2*2^10*c.k,115440477208172+c.lower,115440866494487+c.upper)) = pointBounds67903 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000246
