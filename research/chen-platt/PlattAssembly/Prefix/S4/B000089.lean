import PlattAssemblyKernel
import PlattCertificates.Count131072.C032848
import PlattCertificates.Count131072.C032849
import PlattCertificates.Count131072.C032850
import PlattCertificates.Count131072.C032851
import PlattCertificates.Count131072.C032852
import PlattCertificates.Count131072.C032853
import PlattCertificates.Count131072.C032854
import PlattCertificates.Count131072.C032855
import PlattCertificates.Count131072.C032856
import PlattCertificates.Count131072.C032857
import PlattCertificates.Count131072.C032858
import PlattCertificates.Count131072.C032859
import PlattCertificates.Count131072.C032860
import PlattCertificates.Count131072.C032861
import PlattCertificates.Count131072.C032862
import PlattCertificates.Count131072.C032863
import PlattCertificates.Count131072.C032864
import PlattCertificates.Count131072.C032865
import PlattCertificates.Count131072.C032866
import PlattCertificates.Count131072.C032867
import PlattCertificates.Count131072.C032868
import PlattCertificates.Count131072.C032869
import PlattCertificates.Count131072.C032870
import PlattCertificates.Count131072.C032871
import PlattCertificates.Count131072.C032872
import PlattCertificates.Count131072.C032873
import PlattCertificates.Count131072.C032874
import PlattCertificates.Count131072.C032875
import PlattCertificates.Count131072.C032876
import PlattCertificates.Count131072.C032877
import PlattCertificates.Count131072.C032878
import PlattCertificates.Count131072.C032879
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000089
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts32848 : List PrefixCut := [⟨12,73350458,73350507⟩,
⟨64,387648846,387649100⟩]
theorem checked32848 : checkPrefixCuts (2^48) 4309385217 10 Manual.Count131072.C032848.packed 64 cuts32848 = true := by
 decide +kernel
def pointBounds32848 : List (Nat × Nat × Nat) := [(4309409792,106379937375250,106380321350282)]
theorem point_links_checked32848 : (cuts32848.take 1).map (fun c => (4309385217-1+2*2^10*c.k,106379864024792+c.lower,106380247999775+c.upper)) = pointBounds32848 := by
 decide +kernel
def cuts32849 : List PrefixCut := [⟨14,84451656,84451711⟩,
⟨64,384567275,384567527⟩]
theorem checked32849 : checkPrefixCuts (2^48) 4309516289 10 Manual.Count131072.C032849.packed 64 cuts32849 = true := by
 decide +kernel
def pointBounds32849 : List (Nat × Nat × Nat) := [(4309544960,106380336125294,106380720100586)]
theorem point_links_checked32849 : (cuts32849.take 1).map (fun c => (4309516289-1+2*2^10*c.k,106380251673638+c.lower,106380635648875+c.upper)) = pointBounds32849 := by
 decide +kernel
def cuts32850 : List PrefixCut := [⟨16,94899057,94899120⟩,
⟨64,383118699,383118951⟩]
theorem checked32850 : checkPrefixCuts (2^48) 4309647361 10 Manual.Count131072.C032850.packed 64 cuts32850 = true := by
 decide +kernel
def pointBounds32850 : List (Nat × Nat × Nat) := [(4309680128,106380731139970,106381115115522)]
theorem point_links_checked32850 : (cuts32850.take 1).map (fun c => (4309647361-1+2*2^10*c.k,106380636240913+c.lower,106381020216402+c.upper)) = pointBounds32850 := by
 decide +kernel
def cuts32851 : List PrefixCut := [⟨18,106847927,106847999⟩,
⟨64,383564239,383564489⟩]
theorem checked32851 : checkPrefixCuts (2^48) 4309778433 10 Manual.Count131072.C032851.packed 64 cuts32851 = true := by
 decide +kernel
def pointBounds32851 : List (Nat × Nat × Nat) := [(4309815296,106381126207539,106381510183352)]
theorem point_links_checked32851 : (cuts32851.take 1).map (fun c => (4309778433-1+2*2^10*c.k,106381019359612+c.lower,106381403335353+c.upper)) = pointBounds32851 := by
 decide +kernel
def cuts32852 : List PrefixCut := [⟨20,118469538,118469615⟩,
⟨64,383160692,383160940⟩]
theorem checked32852 : checkPrefixCuts (2^48) 4309909505 10 Manual.Count131072.C032852.packed 64 cuts32852 = true := by
 decide +kernel
def pointBounds32852 : List (Nat × Nat × Nat) := [(4309950464,106381521393389,106381905369457)]
theorem point_links_checked32852 : (cuts32852.take 1).map (fun c => (4309909505-1+2*2^10*c.k,106381402923851+c.lower,106381786899842+c.upper)) = pointBounds32852 := by
 decide +kernel
def cuts32853 : List PrefixCut := [⟨22,137143528,137143613⟩,
⟨64,389940940,389941186⟩]
theorem checked32853 : checkPrefixCuts (2^48) 4310040577 10 Manual.Count131072.C032853.packed 64 cuts32853 = true := by
 decide +kernel
def pointBounds32853 : List (Nat × Nat × Nat) := [(4310085632,106381923228071,106382307204395)]
theorem point_links_checked32853 : (cuts32853.take 1).map (fun c => (4310040577-1+2*2^10*c.k,106381786084543+c.lower,106382170060782+c.upper)) = pointBounds32853 := by
 decide +kernel
def cuts32854 : List PrefixCut := [⟨24,145955389,145955483⟩,
⟨64,388165811,388166062⟩]
theorem checked32854 : checkPrefixCuts (2^48) 4310171649 10 Manual.Count131072.C032854.packed 64 cuts32854 = true := by
 decide +kernel
def pointBounds32854 : List (Nat × Nat × Nat) := [(4310220800,106382321980872,106382705957451)]
theorem point_links_checked32854 : (cuts32854.take 1).map (fun c => (4310171649-1+2*2^10*c.k,106382176025483+c.lower,106382560001968+c.upper)) = pointBounds32854 := by
 decide +kernel
def cuts32855 : List PrefixCut := [⟨26,158946070,158946168⟩,
⟨64,390504868,390505115⟩]
theorem checked32855 : checkPrefixCuts (2^48) 4310302721 10 Manual.Count131072.C032855.packed 64 cuts32855 = true := by
 decide +kernel
def pointBounds32855 : List (Nat × Nat × Nat) := [(4310355968,106382723137364,106383107114198)]
theorem point_links_checked32855 : (cuts32855.take 1).map (fun c => (4310302721-1+2*2^10*c.k,106382564191294+c.lower,106382948168030+c.upper)) = pointBounds32855 := by
 decide +kernel
def cuts32856 : List PrefixCut := [⟨28,168474999,168475106⟩,
⟨64,385073108,385073353⟩]
theorem checked32856 : checkPrefixCuts (2^48) 4310433793 10 Manual.Count131072.C032856.packed 64 cuts32856 = true := by
 decide +kernel
def pointBounds32856 : List (Nat × Nat × Nat) := [(4310491136,106383123171161,106383507148251)]
theorem point_links_checked32856 : (cuts32856.take 1).map (fun c => (4310433793-1+2*2^10*c.k,106382954696162+c.lower,106383338673145+c.upper)) = pointBounds32856 := by
 decide +kernel
def cuts32857 : List PrefixCut := [⟨30,182117176,182117293⟩,
⟨64,387738650,387738899⟩]
theorem checked32857 : checkPrefixCuts (2^48) 4310564865 10 Manual.Count131072.C032857.packed 64 cuts32857 = true := by
 decide +kernel
def pointBounds32857 : List (Nat × Nat × Nat) := [(4310626304,106383521886446,106383905863791)]
theorem point_links_checked32857 : (cuts32857.take 1).map (fun c => (4310564865-1+2*2^10*c.k,106383339769270+c.lower,106383723746498+c.upper)) = pointBounds32857 := by
 decide +kernel
def cuts32858 : List PrefixCut := [⟨32,196672623,196672748⟩,
⟨64,389359227,389359476⟩]
theorem checked32858 : checkPrefixCuts (2^48) 4310695937 10 Manual.Count131072.C032858.packed 64 cuts32858 = true := by
 decide +kernel
def pointBounds32858 : List (Nat × Nat × Nat) := [(4310761472,106383924180543,106384308158145)]
theorem point_links_checked32858 : (cuts32858.take 1).map (fun c => (4310695937-1+2*2^10*c.k,106383727507920+c.lower,106384111485397+c.upper)) = pointBounds32858 := by
 decide +kernel
def cuts32859 : List PrefixCut := [⟨34,207440128,207440263⟩,
⟨64,388498584,388498838⟩]
theorem checked32859 : checkPrefixCuts (2^48) 4310827009 10 Manual.Count131072.C032859.packed 64 cuts32859 = true := by
 decide +kernel
def pointBounds32859 : List (Nat × Nat × Nat) := [(4310896640,106384324307275,106384708285136)]
theorem point_links_checked32859 : (cuts32859.take 1).map (fun c => (4310827009-1+2*2^10*c.k,106384116867147+c.lower,106384500844873+c.upper)) = pointBounds32859 := by
 decide +kernel
def cuts32860 : List PrefixCut := [⟨36,215856410,215856550⟩,
⟨64,383067499,383067750⟩]
theorem checked32860 : checkPrefixCuts (2^48) 4310958081 10 Manual.Count131072.C032860.packed 64 cuts32860 = true := by
 decide +kernel
def pointBounds32860 : List (Nat × Nat × Nat) := [(4311031808,106384721222141,106385105200261)]
theorem point_links_checked32860 : (cuts32860.take 1).map (fun c => (4310958081-1+2*2^10*c.k,106384505365731+c.lower,106384889343711+c.upper)) = pointBounds32860 := by
 decide +kernel
def cuts32861 : List PrefixCut := [⟨38,227471415,227471564⟩,
⟨64,385210418,385210663⟩]
theorem checked32861 : checkPrefixCuts (2^48) 4311089153 10 Manual.Count131072.C032861.packed 64 cuts32861 = true := by
 decide +kernel
def pointBounds32861 : List (Nat × Nat × Nat) := [(4311166976,106385115904645,106385499883025)]
theorem point_links_checked32861 : (cuts32861.take 1).map (fun c => (4311089153-1+2*2^10*c.k,106384888433230+c.lower,106385272411461+c.upper)) = pointBounds32861 := by
 decide +kernel
def cuts32862 : List PrefixCut := [⟨40,242611283,242611441⟩,
⟨64,387614379,387614630⟩]
theorem checked32862 : checkPrefixCuts (2^48) 4311220225 10 Manual.Count131072.C032862.packed 64 cuts32862 = true := by
 decide +kernel
def pointBounds32862 : List (Nat × Nat × Nat) := [(4311302144,106385516254931,106385900233565)]
theorem point_links_checked32862 : (cuts32862.take 1).map (fun c => (4311220225-1+2*2^10*c.k,106385273643648+c.lower,106385657622124+c.upper)) = pointBounds32862 := by
 decide +kernel
def cuts32863 : List PrefixCut := [⟨42,250960453,250960617⟩,
⟨64,385839847,385840095⟩]
theorem checked32863 : checkPrefixCuts (2^48) 4311351297 10 Manual.Count131072.C032863.packed 64 cuts32863 = true := by
 decide +kernel
def pointBounds32863 : List (Nat × Nat × Nat) := [(4311437312,106385912218480,106386296197371)]
theorem point_links_checked32863 : (cuts32863.take 1).map (fun c => (4311351297-1+2*2^10*c.k,106385661258027+c.lower,106386045236754+c.upper)) = pointBounds32863 := by
 decide +kernel
def cuts32864 : List PrefixCut := [⟨44,262377436,262377600⟩,
⟨64,383412627,383412869⟩]
theorem checked32864 : checkPrefixCuts (2^48) 4311482369 10 Manual.Count131072.C032864.packed 64 cuts32864 = true := by
 decide +kernel
def pointBounds32864 : List (Nat × Nat × Nat) := [(4311572480,106386309475310,106386693454449)]
theorem point_links_checked32864 : (cuts32864.take 1).map (fun c => (4311482369-1+2*2^10*c.k,106386047097874+c.lower,106386431076849+c.upper)) = pointBounds32864 := by
 decide +kernel
def cuts32865 : List PrefixCut := [⟨46,272357536,272357712⟩,
⟨64,381834196,381834442⟩]
theorem checked32865 : checkPrefixCuts (2^48) 4311613441 10 Manual.Count131072.C032865.packed 64 cuts32865 = true := by
 decide +kernel
def pointBounds32865 : List (Nat × Nat × Nat) := [(4311707648,106386702868037,106387086847430)]
theorem point_links_checked32865 : (cuts32865.take 1).map (fun c => (4311613441-1+2*2^10*c.k,106386430510501+c.lower,106386814489718+c.upper)) = pointBounds32865 := by
 decide +kernel
def cuts32866 : List PrefixCut := [⟨48,291998490,291998678⟩,
⟨64,389786795,389787044⟩]
theorem checked32866 : checkPrefixCuts (2^48) 4311744513 10 Manual.Count131072.C032866.packed 64 cuts32866 = true := by
 decide +kernel
def pointBounds32866 : List (Nat × Nat × Nat) := [(4311842816,106387104343187,106387488322838)]
theorem point_links_checked32866 : (cuts32866.take 1).map (fun c => (4311744513-1+2*2^10*c.k,106386812344697+c.lower,106387196324160+c.upper)) = pointBounds32866 := by
 decide +kernel
def cuts32867 : List PrefixCut := [⟨50,301389540,301389733⟩,
⟨64,385270775,385271022⟩]
theorem checked32867 : checkPrefixCuts (2^48) 4311875585 10 Manual.Count131072.C032867.packed 64 cuts32867 = true := by
 decide +kernel
def pointBounds32867 : List (Nat × Nat × Nat) := [(4311977984,106387503521032,106387887500937)]
theorem point_links_checked32867 : (cuts32867.take 1).map (fun c => (4311875585-1+2*2^10*c.k,106387202131492+c.lower,106387586111204+c.upper)) = pointBounds32867 := by
 decide +kernel
def cuts32868 : List PrefixCut := [⟨52,312281344,312281545⟩,
⟨64,383888243,383888490⟩]
theorem checked32868 : checkPrefixCuts (2^48) 4312006657 10 Manual.Count131072.C032868.packed 64 cuts32868 = true := by
 decide +kernel
def pointBounds32868 : List (Nat × Nat × Nat) := [(4312113152,106387899683611,106388283663771)]
theorem point_links_checked32868 : (cuts32868.take 1).map (fun c => (4312006657-1+2*2^10*c.k,106387587402267+c.lower,106387971382226+c.upper)) = pointBounds32868 := by
 decide +kernel
def cuts32869 : List PrefixCut := [⟨54,327937513,327937719⟩,
⟨64,388119393,388119639⟩]
theorem checked32869 : checkPrefixCuts (2^48) 4312137729 10 Manual.Count131072.C032869.packed 64 cuts32869 = true := by
 decide +kernel
def pointBounds32869 : List (Nat × Nat × Nat) := [(4312248320,106388299228023,106388683208435)]
theorem point_links_checked32869 : (cuts32869.take 1).map (fun c => (4312137729-1+2*2^10*c.k,106387971290510+c.lower,106388355270716+c.upper)) = pointBounds32869 := by
 decide +kernel
def cuts32870 : List PrefixCut := [⟨56,337000195,337000416⟩,
⟨64,384778694,384778946⟩]
theorem checked32870 : checkPrefixCuts (2^48) 4312268801 10 Manual.Count131072.C032870.packed 64 cuts32870 = true := by
 decide +kernel
def pointBounds32870 : List (Nat × Nat × Nat) := [(4312383488,106388696410098,106389080390771)]
theorem point_links_checked32870 : (cuts32870.take 1).map (fun c => (4312268801-1+2*2^10*c.k,106388359409903+c.lower,106388743390355+c.upper)) = pointBounds32870 := by
 decide +kernel
def cuts32871 : List PrefixCut := [⟨58,347628843,347629069⟩,
⟨64,383461613,383461861⟩]
theorem checked32871 : checkPrefixCuts (2^48) 4312399873 10 Manual.Count131072.C032871.packed 64 cuts32871 = true := by
 decide +kernel
def pointBounds32871 : List (Nat × Nat × Nat) := [(4312518656,106389091817440,106389475798370)]
theorem point_links_checked32871 : (cuts32871.take 1).map (fun c => (4312399873-1+2*2^10*c.k,106388744188597+c.lower,106389128169301+c.upper)) = pointBounds32871 := by
 decide +kernel
def cuts32872 : List PrefixCut := [⟨60,362434006,362434239⟩,
⟨64,386648119,386648367⟩]
theorem checked32872 : checkPrefixCuts (2^48) 4312530945 10 Manual.Count131072.C032872.packed 64 cuts32872 = true := by
 decide +kernel
def pointBounds32872 : List (Nat × Nat × Nat) := [(4312653824,106389490084216,106389874065401)]
theorem point_links_checked32872 : (cuts32872.take 1).map (fun c => (4312530945-1+2*2^10*c.k,106389127650210+c.lower,106389511631162+c.upper)) = pointBounds32872 := by
 decide +kernel
def cuts32873 : List PrefixCut := [⟨62,375867618,375867863⟩,
⟨64,388202728,388202981⟩]
theorem checked32873 : checkPrefixCuts (2^48) 4312662017 10 Manual.Count131072.C032873.packed 64 cuts32873 = true := by
 decide +kernel
def pointBounds32873 : List (Nat × Nat × Nat) := [(4312788992,106389890165947,106390274147392)]
theorem point_links_checked32873 : (cuts32873.take 1).map (fun c => (4312662017-1+2*2^10*c.k,106389514298329+c.lower,106389898279529+c.upper)) = pointBounds32873 := by
 decide +kernel
def cuts32874 : List PrefixCut := [⟨64,385906722,385906967⟩]
theorem checked32874 : checkPrefixCuts (2^48) 4312793089 10 Manual.Count131072.C032874.packed 64 cuts32874 = true := by
 decide +kernel
def pointBounds32874 : List (Nat × Nat × Nat) := [(4312924160,106390288407779,106390672389477)]
theorem point_links_checked32874 : (cuts32874.take 1).map (fun c => (4312793089-1+2*2^10*c.k,106389902501057+c.lower,106390286482510+c.upper)) = pointBounds32874 := by
 decide +kernel
def cuts32875 : List PrefixCut := [⟨64,390202280,390202525⟩]
theorem checked32875 : checkPrefixCuts (2^48) 4312924161 10 Manual.Count131072.C032875.packed 64 cuts32875 = true := by
 decide +kernel
def cuts32876 : List PrefixCut := [⟨2,11616477,11616484⟩,
⟨64,386992650,386992900⟩]
theorem checked32876 : checkPrefixCuts (2^48) 4313055233 10 Manual.Count131072.C032876.packed 64 cuts32876 = true := by
 decide +kernel
def pointBounds32876 : List (Nat × Nat × Nat) := [(4313059328,106390690226536,106391074208486)]
theorem point_links_checked32876 : (cuts32876.take 1).map (fun c => (4313055233-1+2*2^10*c.k,106390678610059+c.lower,106391062592002+c.upper)) = pointBounds32876 := by
 decide +kernel
def cuts32877 : List PrefixCut := [⟨4,23493272,23493288⟩,
⟨64,377453202,377453444⟩]
theorem checked32877 : checkPrefixCuts (2^48) 4313186305 10 Manual.Count131072.C032877.packed 64 cuts32877 = true := by
 decide +kernel
def pointBounds32877 : List (Nat × Nat × Nat) := [(4313194496,106391089095981,106391473078190)]
theorem point_links_checked32877 : (cuts32877.take 1).map (fun c => (4313186305-1+2*2^10*c.k,106391065602709+c.lower,106391449584902+c.upper)) = pointBounds32877 := by
 decide +kernel
def cuts32878 : List PrefixCut := [⟨6,34977794,34977816⟩,
⟨64,386055578,386055818⟩]
theorem checked32878 : checkPrefixCuts (2^48) 4313317377 10 Manual.Count131072.C032878.packed 64 cuts32878 = true := by
 decide +kernel
def pointBounds32878 : List (Nat × Nat × Nat) := [(4313329664,106391478033705,106391862016162)]
theorem point_links_checked32878 : (cuts32878.take 1).map (fun c => (4313317377-1+2*2^10*c.k,106391443055911+c.lower,106391827038346+c.upper)) = pointBounds32878 := by
 decide +kernel
def cuts32879 : List PrefixCut := [⟨8,48745530,48745560⟩,
⟨64,384803991,384804236⟩]
theorem checked32879 : checkPrefixCuts (2^48) 4313448449 10 Manual.Count131072.C032879.packed 64 cuts32879 = true := by
 decide +kernel
def pointBounds32879 : List (Nat × Nat × Nat) := [(4313464832,106391877857019,106392261839724)]
theorem point_links_checked32879 : (cuts32879.take 1).map (fun c => (4313448449-1+2*2^10*c.k,106391829111489+c.lower,106392213094164+c.upper)) = pointBounds32879 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000089
