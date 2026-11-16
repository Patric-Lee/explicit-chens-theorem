import PlattAssemblyKernel
import PlattCertificates.Count131072.C064864
import PlattCertificates.Count131072.C064865
import PlattCertificates.Count131072.C064866
import PlattCertificates.Count131072.C064867
import PlattCertificates.Count131072.C064868
import PlattCertificates.Count131072.C064869
import PlattCertificates.Count131072.C064870
import PlattCertificates.Count131072.C064871
import PlattCertificates.Count131072.C064872
import PlattCertificates.Count131072.C064873
import PlattCertificates.Count131072.C064874
import PlattCertificates.Count131072.C064875
import PlattCertificates.Count131072.C064876
import PlattCertificates.Count131072.C064877
import PlattCertificates.Count131072.C064878
import PlattCertificates.Count131072.C064879
import PlattCertificates.Count131072.C064880
import PlattCertificates.Count131072.C064881
import PlattCertificates.Count131072.C064882
import PlattCertificates.Count131072.C064883
import PlattCertificates.Count131072.C064884
import PlattCertificates.Count131072.C064885
import PlattCertificates.Count131072.C064886
import PlattCertificates.Count131072.C064887
import PlattCertificates.Count131072.C064888
import PlattCertificates.Count131072.C064889
import PlattCertificates.Count131072.C064890
import PlattCertificates.Count131072.C064891
import PlattCertificates.Count131072.C064892
import PlattCertificates.Count131072.C064893
import PlattCertificates.Count131072.C064894
import PlattCertificates.Count131072.C064895
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000152
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64864 : List PrefixCut := [⟨44,129819874,129819952⟩,
⟨64,190940312,190940425⟩]
theorem checked64864 : checkPrefixCuts (2^48) 8505786369 10 Manual.Count131072.C064864.packed 64 cuts64864 = true := by
 decide +kernel
def pointBounds64864 : List (Nat × Nat × Nat) := [(8505876480,114877769262239,114878158221438)]
theorem point_links_checked64864 : (cuts64864.take 1).map (fun c => (8505786369-1+2*2^10*c.k,114877639442365+c.lower,114878028401486+c.upper)) = pointBounds64864 := by
 decide +kernel
def cuts64865 : List PrefixCut := [⟨64,187661335,187661447⟩]
theorem checked64865 : checkPrefixCuts (2^48) 8505917441 10 Manual.Count131072.C064865.packed 64 cuts64865 = true := by
 decide +kernel
def cuts64866 : List PrefixCut := [⟨46,135176590,135176671⟩,
⟨64,188882809,188882922⟩]
theorem checked64866 : checkPrefixCuts (2^48) 8506048513 10 Manual.Count131072.C064866.packed 64 cuts64866 = true := by
 decide +kernel
def pointBounds64866 : List (Nat × Nat × Nat) := [(8506142720,114878153220602,114878542180029)]
theorem point_links_checked64866 : (cuts64866.take 1).map (fun c => (8506048513-1+2*2^10*c.k,114878018044012+c.lower,114878407003358+c.upper)) = pointBounds64866 := by
 decide +kernel
def cuts64867 : List PrefixCut := [⟨64,189045350,189045453⟩]
theorem checked64867 : checkPrefixCuts (2^48) 8506179585 10 Manual.Count131072.C064867.packed 64 cuts64867 = true := by
 decide +kernel
def cuts64868 : List PrefixCut := [⟨48,142518354,142518438⟩,
⟨64,190564570,190564682⟩]
theorem checked64868 : checkPrefixCuts (2^48) 8506310657 10 Manual.Count131072.C064868.packed 64 cuts64868 = true := by
 decide +kernel
def pointBounds64868 : List (Nat × Nat × Nat) := [(8506408960,114878538490525,114878927450171)]
theorem point_links_checked64868 : (cuts64868.take 1).map (fun c => (8506310657-1+2*2^10*c.k,114878395972171+c.lower,114878784931733+c.upper)) = pointBounds64868 := by
 decide +kernel
def cuts64869 : List PrefixCut := [⟨64,187318868,187318976⟩]
theorem checked64869 : checkPrefixCuts (2^48) 8506441729 10 Manual.Count131072.C064869.packed 64 cuts64869 = true := by
 decide +kernel
def cuts64870 : List PrefixCut := [⟨50,147642709,147642789⟩,
⟨64,190426338,190426443⟩]
theorem checked64870 : checkPrefixCuts (2^48) 8506572801 10 Manual.Count131072.C064870.packed 64 cuts64870 = true := by
 decide +kernel
def pointBounds64870 : List (Nat × Nat × Nat) := [(8506675200,114878921498318,114879310458180)]
theorem point_links_checked64870 : (cuts64870.take 1).map (fun c => (8506572801-1+2*2^10*c.k,114878773855609+c.lower,114879162815391+c.upper)) = pointBounds64870 := by
 decide +kernel
def cuts64871 : List PrefixCut := [⟨64,188371939,188372054⟩]
theorem checked64871 : checkPrefixCuts (2^48) 8506703873 10 Manual.Count131072.C064871.packed 64 cuts64871 = true := by
 decide +kernel
def cuts64872 : List PrefixCut := [⟨52,153130719,153130810⟩,
⟨64,188997704,188997817⟩]
theorem checked64872 : checkPrefixCuts (2^48) 8506834945 10 Manual.Count131072.C064872.packed 64 cuts64872 = true := by
 decide +kernel
def pointBounds64872 : List (Nat × Nat × Nat) := [(8506941440,114879305784605,114879694744698)]
theorem point_links_checked64872 : (cuts64872.take 1).map (fun c => (8506834945-1+2*2^10*c.k,114879152653886+c.lower,114879541613888+c.upper)) = pointBounds64872 := by
 decide +kernel
def cuts64873 : List PrefixCut := [⟨64,190715324,190715440⟩]
theorem checked64873 : checkPrefixCuts (2^48) 8506966017 10 Manual.Count131072.C064873.packed 64 cuts64873 = true := by
 decide +kernel
def cuts64874 : List PrefixCut := [⟨54,155971418,155971512⟩,
⟨64,184028853,184028964⟩]
theorem checked64874 : checkPrefixCuts (2^48) 8507097089 10 Manual.Count131072.C064874.packed 64 cuts64874 = true := by
 decide +kernel
def pointBounds64874 : List (Nat × Nat × Nat) := [(8507207680,114879688338332,114880077298657)]
theorem point_links_checked64874 : (cuts64874.take 1).map (fun c => (8507097089-1+2*2^10*c.k,114879532366914+c.lower,114879921327145+c.upper)) = pointBounds64874 := by
 decide +kernel
def cuts64875 : List PrefixCut := [⟨64,188558846,188558957⟩]
theorem checked64875 : checkPrefixCuts (2^48) 8507228161 10 Manual.Count131072.C064875.packed 64 cuts64875 = true := by
 decide +kernel
def cuts64876 : List PrefixCut := [⟨56,163907172,163907266⟩,
⟨64,187100156,187100264⟩]
theorem checked64876 : checkPrefixCuts (2^48) 8507359233 10 Manual.Count131072.C064876.packed 64 cuts64876 = true := by
 decide +kernel
def pointBounds64876 : List (Nat × Nat × Nat) := [(8507473920,114880068861785,114880457822332)]
theorem point_links_checked64876 : (cuts64876.take 1).map (fun c => (8507359233-1+2*2^10*c.k,114879904954613+c.lower,114880293915066+c.upper)) = pointBounds64876 := by
 decide +kernel
def cuts64877 : List PrefixCut := [⟨64,191133695,191133804⟩]
theorem checked64877 : checkPrefixCuts (2^48) 8507490305 10 Manual.Count131072.C064877.packed 64 cuts64877 = true := by
 decide +kernel
def cuts64878 : List PrefixCut := [⟨58,171379249,171379347⟩,
⟨64,190270524,190270633⟩]
theorem checked64878 : checkPrefixCuts (2^48) 8507621377 10 Manual.Count131072.C064878.packed 64 cuts64878 = true := by
 decide +kernel
def pointBounds64878 : List (Nat × Nat × Nat) := [(8507740160,114880454567713,114880843528481)]
theorem point_links_checked64878 : (cuts64878.take 1).map (fun c => (8507621377-1+2*2^10*c.k,114880283188464+c.lower,114880672149134+c.upper)) = pointBounds64878 := by
 decide +kernel
def cuts64879 : List PrefixCut := [⟨64,191557889,191558000⟩]
theorem checked64879 : checkPrefixCuts (2^48) 8507752449 10 Manual.Count131072.C064879.packed 64 cuts64879 = true := by
 decide +kernel
def cuts64880 : List PrefixCut := [⟨60,179115531,179115634⟩,
⟨64,190595511,190595620⟩]
theorem checked64880 : checkPrefixCuts (2^48) 8507883521 10 Manual.Count131072.C064880.packed 64 cuts64880 = true := by
 decide +kernel
def pointBounds64880 : List (Nat × Nat × Nat) := [(8508006400,114880844132408,114881233093401)]
theorem point_links_checked64880 : (cuts64880.take 1).map (fun c => (8507883521-1+2*2^10*c.k,114880665016877+c.lower,114881053977767+c.upper)) = pointBounds64880 := by
 decide +kernel
def cuts64881 : List PrefixCut := [⟨64,190824171,190824282⟩]
theorem checked64881 : checkPrefixCuts (2^48) 8508014593 10 Manual.Count131072.C064881.packed 64 cuts64881 = true := by
 decide +kernel
def cuts64882 : List PrefixCut := [⟨62,184568624,184568728⟩,
⟨64,190192647,190192754⟩]
theorem checked64882 : checkPrefixCuts (2^48) 8508145665 10 Manual.Count131072.C064882.packed 64 cuts64882 = true := by
 decide +kernel
def pointBounds64882 : List (Nat × Nat × Nat) := [(8508272640,114881231005183,114881619966397)]
theorem point_links_checked64882 : (cuts64882.take 1).map (fun c => (8508145665-1+2*2^10*c.k,114881046436559+c.lower,114881435397669+c.upper)) = pointBounds64882 := by
 decide +kernel
def cuts64883 : List PrefixCut := [⟨64,190255878,190255986⟩]
theorem checked64883 : checkPrefixCuts (2^48) 8508276737 10 Manual.Count131072.C064883.packed 64 cuts64883 = true := by
 decide +kernel
def cuts64884 : List PrefixCut := [⟨64,186779362,186779468⟩]
theorem checked64884 : checkPrefixCuts (2^48) 8508407809 10 Manual.Count131072.C064884.packed 64 cuts64884 = true := by
 decide +kernel
def pointBounds64884 : List (Nat × Nat × Nat) := [(8508538880,114881613664446,114882002625877)]
theorem point_links_checked64884 : (cuts64884.take 1).map (fun c => (8508407809-1+2*2^10*c.k,114881426885084+c.lower,114881815846409+c.upper)) = pointBounds64884 := by
 decide +kernel
def cuts64885 : List PrefixCut := [⟨64,191573257,191573368⟩]
theorem checked64885 : checkPrefixCuts (2^48) 8508538881 10 Manual.Count131072.C064885.packed 64 cuts64885 = true := by
 decide +kernel
def cuts64886 : List PrefixCut := [⟨64,189552401,189552518⟩]
theorem checked64886 : checkPrefixCuts (2^48) 8508669953 10 Manual.Count131072.C064886.packed 64 cuts64886 = true := by
 decide +kernel
def cuts64887 : List PrefixCut := [⟨2,5325950,5325953⟩,
⟨64,189847175,189847285⟩]
theorem checked64887 : checkPrefixCuts (2^48) 8508801025 10 Manual.Count131072.C064887.packed 64 cuts64887 = true := by
 decide +kernel
def pointBounds64887 : List (Nat × Nat × Nat) := [(8508805120,114882000116054,114882389077716)]
theorem point_links_checked64887 : (cuts64887.take 1).map (fun c => (8508801025-1+2*2^10*c.k,114881994790104+c.lower,114882383751763+c.upper)) = pointBounds64887 := by
 decide +kernel
def cuts64888 : List PrefixCut := [⟨64,189513464,189513577⟩]
theorem checked64888 : checkPrefixCuts (2^48) 8508932097 10 Manual.Count131072.C064888.packed 64 cuts64888 = true := by
 decide +kernel
def cuts64889 : List PrefixCut := [⟨4,10783887,10783893⟩,
⟨64,188220464,188220576⟩]
theorem checked64889 : checkPrefixCuts (2^48) 8509063169 10 Manual.Count131072.C064889.packed 64 cuts64889 = true := by
 decide +kernel
def pointBounds64889 : List (Nat × Nat × Nat) := [(8509071360,114882384934630,114882773896518)]
theorem point_links_checked64889 : (cuts64889.take 1).map (fun c => (8509063169-1+2*2^10*c.k,114882374150743+c.lower,114882763112625+c.upper)) = pointBounds64889 := by
 decide +kernel
def cuts64890 : List PrefixCut := [⟨64,189540718,189540835⟩]
theorem checked64890 : checkPrefixCuts (2^48) 8509194241 10 Manual.Count131072.C064890.packed 64 cuts64890 = true := by
 decide +kernel
def cuts64891 : List PrefixCut := [⟨6,18523893,18523903⟩,
⟨64,189273163,189273277⟩]
theorem checked64891 : checkPrefixCuts (2^48) 8509325313 10 Manual.Count131072.C064891.packed 64 cuts64891 = true := by
 decide +kernel
def pointBounds64891 : List (Nat × Nat × Nat) := [(8509337600,114882770435818,114883159397939)]
theorem point_links_checked64891 : (cuts64891.take 1).map (fun c => (8509325313-1+2*2^10*c.k,114882751911925+c.lower,114883140874036+c.upper)) = pointBounds64891 := by
 decide +kernel
def cuts64892 : List PrefixCut := [⟨64,190527203,190527311⟩]
theorem checked64892 : checkPrefixCuts (2^48) 8509456385 10 Manual.Count131072.C064892.packed 64 cuts64892 = true := by
 decide +kernel
def cuts64893 : List PrefixCut := [⟨8,24146466,24146480⟩,
⟨64,189498884,189498996⟩]
theorem checked64893 : checkPrefixCuts (2^48) 8509587457 10 Manual.Count131072.C064893.packed 64 cuts64893 = true := by
 decide +kernel
def pointBounds64893 : List (Nat × Nat × Nat) := [(8509603840,114883155858757,114883544821104)]
theorem point_links_checked64893 : (cuts64893.take 1).map (fun c => (8509587457-1+2*2^10*c.k,114883131712291+c.lower,114883520674624+c.upper)) = pointBounds64893 := by
 decide +kernel
def cuts64894 : List PrefixCut := [⟨64,188966724,188966831⟩]
theorem checked64894 : checkPrefixCuts (2^48) 8509718529 10 Manual.Count131072.C064894.packed 64 cuts64894 = true := by
 decide +kernel
def cuts64895 : List PrefixCut := [⟨10,30132532,30132550⟩,
⟨64,191874527,191874637⟩]
theorem checked64895 : checkPrefixCuts (2^48) 8509849601 10 Manual.Count131072.C064895.packed 64 cuts64895 = true := by
 decide +kernel
def pointBounds64895 : List (Nat × Nat × Nat) := [(8509870080,114883540310431,114883929273001)]
theorem point_links_checked64895 : (cuts64895.take 1).map (fun c => (8509849601-1+2*2^10*c.k,114883510177899+c.lower,114883899140451+c.upper)) = pointBounds64895 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000152
