import PlattAssemblyKernel
import PlattCertificates.Count131072.C048864
import PlattCertificates.Count131072.C048865
import PlattCertificates.Count131072.C048866
import PlattCertificates.Count131072.C048867
import PlattCertificates.Count131072.C048868
import PlattCertificates.Count131072.C048869
import PlattCertificates.Count131072.C048870
import PlattCertificates.Count131072.C048871
import PlattCertificates.Count131072.C048872
import PlattCertificates.Count131072.C048873
import PlattCertificates.Count131072.C048874
import PlattCertificates.Count131072.C048875
import PlattCertificates.Count131072.C048876
import PlattCertificates.Count131072.C048877
import PlattCertificates.Count131072.C048878
import PlattCertificates.Count131072.C048879
import PlattCertificates.Count131072.C048880
import PlattCertificates.Count131072.C048881
import PlattCertificates.Count131072.C048882
import PlattCertificates.Count131072.C048883
import PlattCertificates.Count131072.C048884
import PlattCertificates.Count131072.C048885
import PlattCertificates.Count131072.C048886
import PlattCertificates.Count131072.C048887
import PlattCertificates.Count131072.C048888
import PlattCertificates.Count131072.C048889
import PlattCertificates.Count131072.C048890
import PlattCertificates.Count131072.C048891
import PlattCertificates.Count131072.C048892
import PlattCertificates.Count131072.C048893
import PlattCertificates.Count131072.C048894
import PlattCertificates.Count131072.C048895
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000277
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48864 : List PrefixCut := [⟨60,241739943,241740079⟩,
⟨64,257199897,257200044⟩]
theorem checked48864 : checkPrefixCuts (2^48) 6408634369 10 Manual.Count131072.C048864.packed 64 cuts48864 = true := by
 decide +kernel
def pointBounds48864 : List (Nat × Nat × Nat) := [(6408757248,111370937925961,111371324885048)]
theorem point_links_checked48864 : (cuts48864.take 1).map (fun c => (6408634369-1+2*2^10*c.k,111370696186018+c.lower,111371083144969+c.upper)) = pointBounds48864 := by
 decide +kernel
def cuts48865 : List PrefixCut := [⟨64,254998666,254998807⟩]
theorem checked48865 : checkPrefixCuts (2^48) 6408765441 10 Manual.Count131072.C048865.packed 64 cuts48865 = true := by
 decide +kernel
def cuts48866 : List PrefixCut := [⟨30,120470350,120470417⟩,
⟨64,256398853,256399002⟩]
theorem checked48866 : checkPrefixCuts (2^48) 6408896513 10 Manual.Count131072.C048866.packed 64 cuts48866 = true := by
 decide +kernel
def pointBounds48866 : List (Nat × Nat × Nat) := [(6408957952,111371328854931,111371715814237)]
theorem point_links_checked48866 : (cuts48866.take 1).map (fun c => (6408896513-1+2*2^10*c.k,111371208384581+c.lower,111371595343820+c.upper)) = pointBounds48866 := by
 decide +kernel
def cuts48867 : List PrefixCut := [⟨64,254065947,254066093⟩]
theorem checked48867 : checkPrefixCuts (2^48) 6409027585 10 Manual.Count131072.C048867.packed 64 cuts48867 = true := by
 decide +kernel
def pointBounds48867 : List (Nat × Nat × Nat) := [(6409158656,111371718849381,111372105808915)]
theorem point_links_checked48867 : (cuts48867.take 1).map (fun c => (6409027585-1+2*2^10*c.k,111371464783434+c.lower,111371851742822+c.upper)) = pointBounds48867 := by
 decide +kernel
def cuts48868 : List PrefixCut := [⟨64,256476201,256476343⟩]
theorem checked48868 : checkPrefixCuts (2^48) 6409158657 10 Manual.Count131072.C048868.packed 64 cuts48868 = true := by
 decide +kernel
def cuts48869 : List PrefixCut := [⟨34,134208725,134208806⟩,
⟨64,254275112,254275263⟩]
theorem checked48869 : checkPrefixCuts (2^48) 6409289729 10 Manual.Count131072.C048869.packed 64 cuts48869 = true := by
 decide +kernel
def pointBounds48869 : List (Nat × Nat × Nat) := [(6409359360,111372109534307,111372496494064)]
theorem point_links_checked48869 : (cuts48869.take 1).map (fun c => (6409289729-1+2*2^10*c.k,111371975325582+c.lower,111372362285258+c.upper)) = pointBounds48869 := by
 decide +kernel
def cuts48870 : List PrefixCut := [⟨64,253830781,253830932⟩]
theorem checked48870 : checkPrefixCuts (2^48) 6409420801 10 Manual.Count131072.C048870.packed 64 cuts48870 = true := by
 decide +kernel
def cuts48871 : List PrefixCut := [⟨4,15545869,15545877⟩,
⟨64,255450421,255450567⟩]
theorem checked48871 : checkPrefixCuts (2^48) 6409551873 10 Manual.Count131072.C048871.packed 64 cuts48871 = true := by
 decide +kernel
def pointBounds48871 : List (Nat × Nat × Nat) := [(6409560064,111372498977344,111372885937330)]
theorem point_links_checked48871 : (cuts48871.take 1).map (fun c => (6409551873-1+2*2^10*c.k,111372483431475+c.lower,111372870391453+c.upper)) = pointBounds48871 := by
 decide +kernel
def cuts48872 : List PrefixCut := [⟨38,151282848,151282938⟩,
⟨64,252415170,252415319⟩]
theorem checked48872 : checkPrefixCuts (2^48) 6409682945 10 Manual.Count131072.C048872.packed 64 cuts48872 = true := by
 decide +kernel
def pointBounds48872 : List (Nat × Nat × Nat) := [(6409760768,111372890164744,111373277124958)]
theorem point_links_checked48872 : (cuts48872.take 1).map (fun c => (6409682945-1+2*2^10*c.k,111372738881896+c.lower,111373125842020+c.upper)) = pointBounds48872 := by
 decide +kernel
def cuts48873 : List PrefixCut := [⟨64,256493881,256494027⟩]
theorem checked48873 : checkPrefixCuts (2^48) 6409814017 10 Manual.Count131072.C048873.packed 64 cuts48873 = true := by
 decide +kernel
def cuts48874 : List PrefixCut := [⟨8,31924141,31924159⟩,
⟨64,256269067,256269213⟩]
theorem checked48874 : checkPrefixCuts (2^48) 6409945089 10 Manual.Count131072.C048874.packed 64 cuts48874 = true := by
 decide +kernel
def pointBounds48874 : List (Nat × Nat × Nat) := [(6409961472,111373279715088,111373666675525)]
theorem point_links_checked48874 : (cuts48874.take 1).map (fun c => (6409945089-1+2*2^10*c.k,111373247790947+c.lower,111373634751366+c.upper)) = pointBounds48874 := by
 decide +kernel
def cuts48875 : List PrefixCut := [⟨42,166686258,166686354⟩,
⟨64,255209979,255210121⟩]
theorem checked48875 : checkPrefixCuts (2^48) 6410076161 10 Manual.Count131072.C048875.packed 64 cuts48875 = true := by
 decide +kernel
def pointBounds48875 : List (Nat × Nat × Nat) := [(6410162176,111373670746272,111374057706933)]
theorem point_links_checked48875 : (cuts48875.take 1).map (fun c => (6410076161-1+2*2^10*c.k,111373504060014+c.lower,111373891020579+c.upper)) = pointBounds48875 := by
 decide +kernel
def cuts48876 : List PrefixCut := [⟨64,255512152,255512296⟩]
theorem checked48876 : checkPrefixCuts (2^48) 6410207233 10 Manual.Count131072.C048876.packed 64 cuts48876 = true := by
 decide +kernel
def cuts48877 : List PrefixCut := [⟨12,47861287,47861315⟩,
⟨64,255375186,255375330⟩]
theorem checked48877 : checkPrefixCuts (2^48) 6410338305 10 Manual.Count131072.C048877.packed 64 cuts48877 = true := by
 decide +kernel
def pointBounds48877 : List (Nat × Nat × Nat) := [(6410362880,111374062643432,111374449604311)]
theorem point_links_checked48877 : (cuts48877.take 1).map (fun c => (6410338305-1+2*2^10*c.k,111374014782145+c.lower,111374401742996+c.upper)) = pointBounds48877 := by
 decide +kernel
def cuts48878 : List PrefixCut := [⟨46,181209565,181209669⟩,
⟨64,251945117,251945261⟩]
theorem checked48878 : checkPrefixCuts (2^48) 6410469377 10 Manual.Count131072.C048878.packed 64 cuts48878 = true := by
 decide +kernel
def pointBounds48878 : List (Nat × Nat × Nat) := [(6410563584,111374451366896,111374838327995)]
theorem point_links_checked48878 : (cuts48878.take 1).map (fun c => (6410469377-1+2*2^10*c.k,111374270157331+c.lower,111374657118326+c.upper)) = pointBounds48878 := by
 decide +kernel
def cuts48879 : List PrefixCut := [⟨64,256725850,256725995⟩]
theorem checked48879 : checkPrefixCuts (2^48) 6410600449 10 Manual.Count131072.C048879.packed 64 cuts48879 = true := by
 decide +kernel
def cuts48880 : List PrefixCut := [⟨16,62435354,62435391⟩,
⟨64,256764506,256764651⟩]
theorem checked48880 : checkPrefixCuts (2^48) 6410731521 10 Manual.Count131072.C048880.packed 64 cuts48880 = true := by
 decide +kernel
def pointBounds48880 : List (Nat × Nat × Nat) := [(6410764288,111374841263652,111375228224973)]
theorem point_links_checked48880 : (cuts48880.take 1).map (fun c => (6410731521-1+2*2^10*c.k,111374778828298+c.lower,111375165789582+c.upper)) = pointBounds48880 := by
 decide +kernel
def cuts48881 : List PrefixCut := [⟨50,200121626,200121743⟩,
⟨64,254783514,254783662⟩]
theorem checked48881 : checkPrefixCuts (2^48) 6410862593 10 Manual.Count131072.C048881.packed 64 cuts48881 = true := by
 decide +kernel
def pointBounds48881 : List (Nat × Nat × Nat) := [(6410964992,111375235714430,111375622675976)]
theorem point_links_checked48881 : (cuts48881.take 1).map (fun c => (6410862593-1+2*2^10*c.k,111375035592804+c.lower,111375422554233+c.upper)) = pointBounds48881 := by
 decide +kernel
def cuts48882 : List PrefixCut := [⟨64,254251460,254251605⟩]
theorem checked48882 : checkPrefixCuts (2^48) 6410993665 10 Manual.Count131072.C048882.packed 64 cuts48882 = true := by
 decide +kernel
def cuts48883 : List PrefixCut := [⟨20,78895479,78895528⟩,
⟨64,255958474,255958627⟩]
theorem checked48883 : checkPrefixCuts (2^48) 6411124737 10 Manual.Count131072.C048883.packed 64 cuts48883 = true := by
 decide +kernel
def pointBounds48883 : List (Nat × Nat × Nat) := [(6411165696,111375623523257,111376010485028)]
theorem point_links_checked48883 : (cuts48883.take 1).map (fun c => (6411124737-1+2*2^10*c.k,111375544627778+c.lower,111375931589500+c.upper)) = pointBounds48883 := by
 decide +kernel
def cuts48884 : List PrefixCut := [⟨54,215431330,215431451⟩,
⟨64,255382525,255382667⟩]
theorem checked48884 : checkPrefixCuts (2^48) 6411255809 10 Manual.Count131072.C048884.packed 64 cuts48884 = true := by
 decide +kernel
def pointBounds48884 : List (Nat × Nat × Nat) := [(6411366400,111376016017582,111376402979578)]
theorem point_links_checked48884 : (cuts48884.take 1).map (fun c => (6411255809-1+2*2^10*c.k,111375800586252+c.lower,111376187548127+c.upper)) = pointBounds48884 := by
 decide +kernel
def cuts48885 : List PrefixCut := [⟨64,256035859,256036008⟩]
theorem checked48885 : checkPrefixCuts (2^48) 6411386881 10 Manual.Count131072.C048885.packed 64 cuts48885 = true := by
 decide +kernel
def cuts48886 : List PrefixCut := [⟨24,94387740,94387794⟩,
⟨64,253572137,253572280⟩]
theorem checked48886 : checkPrefixCuts (2^48) 6411517953 10 Manual.Count131072.C048886.packed 64 cuts48886 = true := by
 decide +kernel
def pointBounds48886 : List (Nat × Nat × Nat) := [(6411567104,111376406392376,111376793354596)]
theorem point_links_checked48886 : (cuts48886.take 1).map (fun c => (6411517953-1+2*2^10*c.k,111376312004636+c.lower,111376698966802+c.upper)) = pointBounds48886 := by
 decide +kernel
def cuts48887 : List PrefixCut := [⟨58,227578320,227578449⟩,
⟨64,250845156,250845300⟩]
theorem checked48887 : checkPrefixCuts (2^48) 6411649025 10 Manual.Count131072.C048887.packed 64 cuts48887 = true := by
 decide +kernel
def pointBounds48887 : List (Nat × Nat × Nat) := [(6411767808,111376793155093,111377180117531)]
theorem point_links_checked48887 : (cuts48887.take 1).map (fun c => (6411649025-1+2*2^10*c.k,111376565576773+c.lower,111376952539082+c.upper)) = pointBounds48887 := by
 decide +kernel
def cuts48888 : List PrefixCut := [⟨64,258478525,258478675⟩]
theorem checked48888 : checkPrefixCuts (2^48) 6411780097 10 Manual.Count131072.C048888.packed 64 cuts48888 = true := by
 decide +kernel
def cuts48889 : List PrefixCut := [⟨28,113653362,113653427⟩,
⟨64,257200175,257200319⟩]
theorem checked48889 : checkPrefixCuts (2^48) 6411911169 10 Manual.Count131072.C048889.packed 64 cuts48889 = true := by
 decide +kernel
def pointBounds48889 : List (Nat × Nat × Nat) := [(6411968512,111377188553816,111377575516484)]
theorem point_links_checked48889 : (cuts48889.take 1).map (fun c => (6411911169-1+2*2^10*c.k,111377074900454+c.lower,111377461863057+c.upper)) = pointBounds48889 := by
 decide +kernel
def cuts48890 : List PrefixCut := [⟨62,248152106,248152249⟩,
⟨64,255658488,255658635⟩]
theorem checked48890 : checkPrefixCuts (2^48) 6412042241 10 Manual.Count131072.C048890.packed 64 cuts48890 = true := by
 decide +kernel
def pointBounds48890 : List (Nat × Nat × Nat) := [(6412169216,111377580252735,111377967215625)]
theorem point_links_checked48890 : (cuts48890.take 1).map (fun c => (6412042241-1+2*2^10*c.k,111377332100629+c.lower,111377719063376+c.upper)) = pointBounds48890 := by
 decide +kernel
def cuts48891 : List PrefixCut := [⟨64,257672515,257672657⟩]
theorem checked48891 : checkPrefixCuts (2^48) 6412173313 10 Manual.Count131072.C048891.packed 64 cuts48891 = true := by
 decide +kernel
def cuts48892 : List PrefixCut := [⟨32,128614800,128614870⟩,
⟨64,254506766,254506907⟩]
theorem checked48892 : checkPrefixCuts (2^48) 6412304385 10 Manual.Count131072.C048892.packed 64 cuts48892 = true := by
 decide +kernel
def pointBounds48892 : List (Nat × Nat × Nat) := [(6412369920,111377974046432,111378361009538)]
theorem point_links_checked48892 : (cuts48892.take 1).map (fun c => (6412304385-1+2*2^10*c.k,111377845431632+c.lower,111378232394668+c.upper)) = pointBounds48892 := by
 decide +kernel
def cuts48893 : List PrefixCut := [⟨64,254808833,254808976⟩]
theorem checked48893 : checkPrefixCuts (2^48) 6412435457 10 Manual.Count131072.C048893.packed 64 cuts48893 = true := by
 decide +kernel
def cuts48894 : List PrefixCut := [⟨2,7725388,7725392⟩,
⟨64,253794051,253794193⟩]
theorem checked48894 : checkPrefixCuts (2^48) 6412566529 10 Manual.Count131072.C048894.packed 64 cuts48894 = true := by
 decide +kernel
def pointBounds48894 : List (Nat × Nat × Nat) := [(6412570624,111378362472619,111378749435943)]
theorem point_links_checked48894 : (cuts48894.take 1).map (fun c => (6412566529-1+2*2^10*c.k,111378354747231+c.lower,111378741710551+c.upper)) = pointBounds48894 := by
 decide +kernel
def cuts48895 : List PrefixCut := [⟨36,143530488,143530568⟩,
⟨64,253218265,253218405⟩]
theorem checked48895 : checkPrefixCuts (2^48) 6412697601 10 Manual.Count131072.C048895.packed 64 cuts48895 = true := by
 decide +kernel
def pointBounds48895 : List (Nat × Nat × Nat) := [(6412771328,111378752071770,111379139035312)]
theorem point_links_checked48895 : (cuts48895.take 1).map (fun c => (6412697601-1+2*2^10*c.k,111378608541282+c.lower,111378995504744+c.upper)) = pointBounds48895 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000277
