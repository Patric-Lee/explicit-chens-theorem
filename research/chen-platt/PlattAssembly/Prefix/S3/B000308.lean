import PlattAssemblyKernel
import PlattCertificates.Count131072.C029856
import PlattCertificates.Count131072.C029857
import PlattCertificates.Count131072.C029858
import PlattCertificates.Count131072.C029859
import PlattCertificates.Count131072.C029860
import PlattCertificates.Count131072.C029861
import PlattCertificates.Count131072.C029862
import PlattCertificates.Count131072.C029863
import PlattCertificates.Count131072.C029864
import PlattCertificates.Count131072.C029865
import PlattCertificates.Count131072.C029866
import PlattCertificates.Count131072.C029867
import PlattCertificates.Count131072.C029868
import PlattCertificates.Count131072.C029869
import PlattCertificates.Count131072.C029870
import PlattCertificates.Count131072.C029871
import PlattCertificates.Count131072.C029872
import PlattCertificates.Count131072.C029873
import PlattCertificates.Count131072.C029874
import PlattCertificates.Count131072.C029875
import PlattCertificates.Count131072.C029876
import PlattCertificates.Count131072.C029877
import PlattCertificates.Count131072.C029878
import PlattCertificates.Count131072.C029879
import PlattCertificates.Count131072.C029880
import PlattCertificates.Count131072.C029881
import PlattCertificates.Count131072.C029882
import PlattCertificates.Count131072.C029883
import PlattCertificates.Count131072.C029884
import PlattCertificates.Count131072.C029885
import PlattCertificates.Count131072.C029886
import PlattCertificates.Count131072.C029887
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000308
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts29856 : List PrefixCut := [⟨45,146872433,146872515⟩,
⟨128,423654787,423655021⟩]
theorem checked29856 : checkPrefixCuts (2^48) 3917217793 9 Manual.Count131072.C029856.packed 128 cuts29856 = true := by
 decide +kernel
def pointBounds29856 : List (Nat × Nat × Nat) := [(3917263872,105166883446904,105167266733918)]
theorem point_links_checked29856 : (cuts29856.take 1).map (fun c => (3917217793-1+2*2^9*c.k,105166736574471+c.lower,105167119861403+c.upper)) = pointBounds29856 := by
 decide +kernel
def cuts29857 : List PrefixCut := [⟨37,124449516,124449586⟩,
⟨128,427305117,427305358⟩]
theorem checked29857 : checkPrefixCuts (2^48) 3917348865 9 Manual.Count131072.C029857.packed 128 cuts29857 = true := by
 decide +kernel
def pointBounds29857 : List (Nat × Nat × Nat) := [(3917386752,105167284678774,105167667966010)]
theorem point_links_checked29857 : (cuts29857.take 1).map (fun c => (3917348865-1+2*2^9*c.k,105167160229258+c.lower,105167543516424+c.upper)) = pointBounds29857 := by
 decide +kernel
def cuts29858 : List PrefixCut := [⟨29,95489632,95489683⟩,
⟨128,428152997,428153233⟩]
theorem checked29858 : checkPrefixCuts (2^48) 3917479937 9 Manual.Count131072.C029858.packed 128 cuts29858 = true := by
 decide +kernel
def pointBounds29858 : List (Nat × Nat × Nat) := [(3917509632,105167683024007,105168066311465)]
theorem point_links_checked29858 : (cuts29858.take 1).map (fun c => (3917479937-1+2*2^9*c.k,105167587534375+c.lower,105167970821782+c.upper)) = pointBounds29858 := by
 decide +kernel
def cuts29859 : List PrefixCut := [⟨21,70770687,70770728⟩,
⟨128,426198817,426199058⟩]
theorem checked29859 : checkPrefixCuts (2^48) 3917611009 9 Manual.Count131072.C029859.packed 128 cuts29859 = true := by
 decide +kernel
def pointBounds29859 : List (Nat × Nat × Nat) := [(3917632512,105168086458059,105168469745743)]
theorem point_links_checked29859 : (cuts29859.take 1).map (fun c => (3917611009-1+2*2^9*c.k,105168015687372+c.lower,105168398975015+c.upper)) = pointBounds29859 := by
 decide +kernel
def cuts29860 : List PrefixCut := [⟨13,41024112,41024135⟩,
⟨128,427262190,427262426⟩]
theorem checked29860 : checkPrefixCuts (2^48) 3917742081 9 Manual.Count131072.C029860.packed 128 cuts29860 = true := by
 decide +kernel
def pointBounds29860 : List (Nat × Nat × Nat) := [(3917755392,105168482910301,105168866198208)]
theorem point_links_checked29860 : (cuts29860.take 1).map (fun c => (3917742081-1+2*2^9*c.k,105168441886189+c.lower,105168825174073+c.upper)) = pointBounds29860 := by
 decide +kernel
def cuts29861 : List PrefixCut := [⟨5,15877470,15877480⟩,
⟨125,415609536,415609775⟩,
⟨128,426313908,426314153⟩]
theorem checked29861 : checkPrefixCuts (2^48) 3917873153 9 Manual.Count131072.C029861.packed 128 cuts29861 = true := by
 decide +kernel
def pointBounds29861 : List (Nat × Nat × Nat) := [(3917878272,105168885025849,105169268313979),(3918001152,105169284757915,105169668046274)]
theorem point_links_checked29861 : (cuts29861.take 2).map (fun c => (3917873153-1+2*2^9*c.k,105168869148379+c.lower,105169252436499+c.upper)) = pointBounds29861 := by
 decide +kernel
def cuts29862 : List PrefixCut := [⟨117,385135792,385136005⟩,
⟨128,421414536,421414769⟩]
theorem checked29862 : checkPrefixCuts (2^48) 3918004225 9 Manual.Count131072.C029862.packed 128 cuts29862 = true := by
 decide +kernel
def pointBounds29862 : List (Nat × Nat × Nat) := [(3918124032,105169680598079,105170063886657)]
theorem point_links_checked29862 : (cuts29862.take 1).map (fun c => (3918004225-1+2*2^9*c.k,105169295462287+c.lower,105169678750652+c.upper)) = pointBounds29862 := by
 decide +kernel
def cuts29863 : List PrefixCut := [⟨109,359549020,359549225⟩,
⟨128,423986600,423986840⟩]
theorem checked29863 : checkPrefixCuts (2^48) 3918135297 9 Manual.Count131072.C029863.packed 128 cuts29863 = true := by
 decide +kernel
def pointBounds29863 : List (Nat × Nat × Nat) := [(3918246912,105170076425843,105170459714646)]
theorem point_links_checked29863 : (cuts29863.take 1).map (fun c => (3918135297-1+2*2^9*c.k,105169716876823+c.lower,105170100165421+c.upper)) = pointBounds29863 := by
 decide +kernel
def cuts29864 : List PrefixCut := [⟨101,335113263,335113452⟩,
⟨128,423828799,423829039⟩]
theorem checked29864 : checkPrefixCuts (2^48) 3918266369 9 Manual.Count131072.C029864.packed 128 cuts29864 = true := by
 decide +kernel
def pointBounds29864 : List (Nat × Nat × Nat) := [(3918369792,105170475976686,105170859265713)]
theorem point_links_checked29864 : (cuts29864.take 1).map (fun c => (3918266369-1+2*2^9*c.k,105170140863423+c.lower,105170524152261+c.upper)) = pointBounds29864 := by
 decide +kernel
def cuts29865 : List PrefixCut := [⟨93,311325648,311325829⟩,
⟨128,432003597,432003846⟩]
theorem checked29865 : checkPrefixCuts (2^48) 3918397441 9 Manual.Count131072.C029865.packed 128 cuts29865 = true := by
 decide +kernel
def pointBounds29865 : List (Nat × Nat × Nat) := [(3918492672,105170876017870,105171259307129)]
theorem point_links_checked29865 : (cuts29865.take 1).map (fun c => (3918397441-1+2*2^9*c.k,105170564692222+c.lower,105170947981300+c.upper)) = pointBounds29865 := by
 decide +kernel
def cuts29866 : List PrefixCut := [⟨85,279566178,279566339⟩,
⟨128,423656726,423656968⟩]
theorem checked29866 : checkPrefixCuts (2^48) 3918528513 9 Manual.Count131072.C029866.packed 128 cuts29866 = true := by
 decide +kernel
def pointBounds29866 : List (Nat × Nat × Nat) := [(3918615552,105171276261997,105171659551485)]
theorem point_links_checked29866 : (cuts29866.take 1).map (fun c => (3918528513-1+2*2^9*c.k,105170996695819+c.lower,105171379985146+c.upper)) = pointBounds29866 := by
 decide +kernel
def cuts29867 : List PrefixCut := [⟨77,254488939,254489087⟩,
⟨128,428095899,428096143⟩]
theorem checked29867 : checkPrefixCuts (2^48) 3918659585 9 Manual.Count131072.C029867.packed 128 cuts29867 = true := by
 decide +kernel
def pointBounds29867 : List (Nat × Nat × Nat) := [(3918738432,105171674841484,105172058131201)]
theorem point_links_checked29867 : (cuts29867.take 1).map (fun c => (3918659585-1+2*2^9*c.k,105171420352545+c.lower,105171803642114+c.upper)) = pointBounds29867 := by
 decide +kernel
def cuts29868 : List PrefixCut := [⟨69,228551365,228551495⟩,
⟨128,425495874,425496113⟩]
theorem checked29868 : checkPrefixCuts (2^48) 3918790657 9 Manual.Count131072.C029868.packed 128 cuts29868 = true := by
 decide +kernel
def pointBounds29868 : List (Nat × Nat × Nat) := [(3918861312,105172076999809,105172460289752)]
theorem point_links_checked29868 : (cuts29868.take 1).map (fun c => (3918790657-1+2*2^9*c.k,105171848448444+c.lower,105172231738257+c.upper)) = pointBounds29868 := by
 decide +kernel
def cuts29869 : List PrefixCut := [⟨61,202471856,202471971⟩,
⟨128,428570063,428570306⟩]
theorem checked29869 : checkPrefixCuts (2^48) 3918921729 9 Manual.Count131072.C029869.packed 128 cuts29869 = true := by
 decide +kernel
def pointBounds29869 : List (Nat × Nat × Nat) := [(3918984192,105172476416174,105172859706341)]
theorem point_links_checked29869 : (cuts29869.take 1).map (fun c => (3918921729-1+2*2^9*c.k,105172273944318+c.lower,105172657234370+c.upper)) = pointBounds29869 := by
 decide +kernel
def cuts29870 : List PrefixCut := [⟨53,175891286,175891388⟩,
⟨128,424964715,424964954⟩]
theorem checked29870 : checkPrefixCuts (2^48) 3919052801 9 Manual.Count131072.C029870.packed 128 cuts29870 = true := by
 decide +kernel
def pointBounds29870 : List (Nat × Nat × Nat) := [(3919107072,105172878405667,105173261696064)]
theorem point_links_checked29870 : (cuts29870.take 1).map (fun c => (3919052801-1+2*2^9*c.k,105172702514381+c.lower,105173085804676+c.upper)) = pointBounds29870 := by
 decide +kernel
def cuts29871 : List PrefixCut := [⟨45,147660588,147660673⟩,
⟨128,418486805,418487045⟩]
theorem checked29871 : checkPrefixCuts (2^48) 3919183873 9 Manual.Count131072.C029871.packed 128 cuts29871 = true := by
 decide +kernel
def pointBounds29871 : List (Nat × Nat × Nat) := [(3919229952,105173275139684,105173658430303)]
theorem point_links_checked29871 : (cuts29871.take 1).map (fun c => (3919183873-1+2*2^9*c.k,105173127479096+c.lower,105173510769630+c.upper)) = pointBounds29871 := by
 decide +kernel
def cuts29872 : List PrefixCut := [⟨37,125033444,125033511⟩,
⟨128,433913283,433913524⟩]
theorem checked29872 : checkPrefixCuts (2^48) 3919314945 9 Manual.Count131072.C029872.packed 128 cuts29872 = true := by
 decide +kernel
def pointBounds29872 : List (Nat × Nat × Nat) := [(3919352832,105173670999345,105174054290186)]
theorem point_links_checked29872 : (cuts29872.take 1).map (fun c => (3919314945-1+2*2^9*c.k,105173545965901+c.lower,105173929256675+c.upper)) = pointBounds29872 := by
 decide +kernel
def cuts29873 : List PrefixCut := [⟨29,95657177,95657229⟩,
⟨128,427938259,427938499⟩]
theorem checked29873 : checkPrefixCuts (2^48) 3919446017 9 Manual.Count131072.C029873.packed 128 cuts29873 = true := by
 decide +kernel
def pointBounds29873 : List (Nat × Nat × Nat) := [(3919475712,105174075536361,105174458827428)]
theorem point_links_checked29873 : (cuts29873.take 1).map (fun c => (3919446017-1+2*2^9*c.k,105173979879184+c.lower,105174363170199+c.upper)) = pointBounds29873 := by
 decide +kernel
def cuts29874 : List PrefixCut := [⟨21,66857319,66857357⟩,
⟨128,420096511,420096750⟩]
theorem checked29874 : checkPrefixCuts (2^48) 3919577089 9 Manual.Count131072.C029874.packed 128 cuts29874 = true := by
 decide +kernel
def pointBounds29874 : List (Nat × Nat × Nat) := [(3919598592,105174474674762,105174857966055)]
theorem point_links_checked29874 : (cuts29874.take 1).map (fun c => (3919577089-1+2*2^9*c.k,105174407817443+c.lower,105174791108698+c.upper)) = pointBounds29874 := by
 decide +kernel
def cuts29875 : List PrefixCut := [⟨13,44378605,44378630⟩,
⟨128,432720841,432721086⟩]
theorem checked29875 : checkPrefixCuts (2^48) 3919708161 9 Manual.Count131072.C029875.packed 128 cuts29875 = true := by
 decide +kernel
def pointBounds29875 : List (Nat × Nat × Nat) := [(3919721472,105174872292559,105175255584078)]
theorem point_links_checked29875 : (cuts29875.take 1).map (fun c => (3919708161-1+2*2^9*c.k,105174827913954+c.lower,105175211205448+c.upper)) = pointBounds29875 := by
 decide +kernel
def cuts29876 : List PrefixCut := [⟨5,16372160,16372169⟩,
⟨125,412672414,412672647⟩,
⟨128,422294336,422294574⟩]
theorem checked29876 : checkPrefixCuts (2^48) 3919839233 9 Manual.Count131072.C029876.packed 128 cuts29876 = true := by
 decide +kernel
def pointBounds29876 : List (Nat × Nat × Nat) := [(3919844352,105175277006955,105175660298703),(3919967232,105175673307209,105176056599181)]
theorem point_links_checked29876 : (cuts29876.take 2).map (fun c => (3919839233-1+2*2^9*c.k,105175260634795+c.lower,105175643926534+c.upper)) = pointBounds29876 := by
 decide +kernel
def cuts29877 : List PrefixCut := [⟨117,386235190,386235409⟩,
⟨128,424362617,424362858⟩]
theorem checked29877 : checkPrefixCuts (2^48) 3919970305 9 Manual.Count131072.C029877.packed 128 cuts29877 = true := by
 decide +kernel
def pointBounds29877 : List (Nat × Nat × Nat) := [(3920090112,105176069164321,105176452456517)]
theorem point_links_checked29877 : (cuts29877.take 1).map (fun c => (3919970305-1+2*2^9*c.k,105175682929131+c.lower,105176066221108+c.upper)) = pointBounds29877 := by
 decide +kernel
def cuts29878 : List PrefixCut := [⟨109,363533251,363533459⟩,
⟨128,429589935,429590175⟩]
theorem checked29878 : checkPrefixCuts (2^48) 3920101377 9 Manual.Count131072.C029878.packed 128 cuts29878 = true := by
 decide +kernel
def pointBounds29878 : List (Nat × Nat × Nat) := [(3920212992,105176470824999,105176854117425)]
theorem point_links_checked29878 : (cuts29878.take 1).map (fun c => (3920101377-1+2*2^9*c.k,105176107291748+c.lower,105176490583966+c.upper)) = pointBounds29878 := by
 decide +kernel
def cuts29879 : List PrefixCut := [⟨101,333581017,333581203⟩,
⟨128,428067733,428067970⟩]
theorem checked29879 : checkPrefixCuts (2^48) 3920232449 9 Manual.Count131072.C029879.packed 128 cuts29879 = true := by
 decide +kernel
def pointBounds29879 : List (Nat × Nat × Nat) := [(3920335872,105176870462700,105177253755344)]
theorem point_links_checked29879 : (cuts29879.take 1).map (fun c => (3920232449-1+2*2^9*c.k,105176536881683+c.lower,105176920174141+c.upper)) = pointBounds29879 := by
 decide +kernel
def cuts29880 : List PrefixCut := [⟨93,311456671,311456844⟩,
⟨128,425612459,425612696⟩]
theorem checked29880 : checkPrefixCuts (2^48) 3920363521 9 Manual.Count131072.C029880.packed 128 cuts29880 = true := by
 decide +kernel
def pointBounds29880 : List (Nat × Nat × Nat) := [(3920458752,105177276406087,105177659698955)]
theorem point_links_checked29880 : (cuts29880.take 1).map (fun c => (3920363521-1+2*2^9*c.k,105176964949416+c.lower,105177348242111+c.upper)) = pointBounds29880 := by
 decide +kernel
def cuts29881 : List PrefixCut := [⟨85,278492685,278492843⟩,
⟨128,422080214,422080453⟩]
theorem checked29881 : checkPrefixCuts (2^48) 3920494593 9 Manual.Count131072.C029881.packed 128 cuts29881 = true := by
 decide +kernel
def pointBounds29881 : List (Nat × Nat × Nat) := [(3920581632,105177669054560,105178052347650)]
theorem point_links_checked29881 : (cuts29881.take 1).map (fun c => (3920494593-1+2*2^9*c.k,105177390561875+c.lower,105177773854807+c.upper)) = pointBounds29881 := by
 decide +kernel
def cuts29882 : List PrefixCut := [⟨77,258238116,258238255⟩,
⟨128,427522331,427522566⟩]
theorem checked29882 : checkPrefixCuts (2^48) 3920625665 9 Manual.Count131072.C029882.packed 128 cuts29882 = true := by
 decide +kernel
def pointBounds29882 : List (Nat × Nat × Nat) := [(3920704512,105178070880205,105178454173515)]
theorem point_links_checked29882 : (cuts29882.take 1).map (fun c => (3920625665-1+2*2^9*c.k,105177812642089+c.lower,105178195935260+c.upper)) = pointBounds29882 := by
 decide +kernel
def cuts29883 : List PrefixCut := [⟨69,231739154,231739283⟩,
⟨128,434471624,434471866⟩]
theorem checked29883 : checkPrefixCuts (2^48) 3920756737 9 Manual.Count131072.C029883.packed 128 cuts29883 = true := by
 decide +kernel
def pointBounds29883 : List (Nat × Nat × Nat) := [(3920827392,105178471903574,105178855197109)]
theorem point_links_checked29883 : (cuts29883.take 1).map (fun c => (3920756737-1+2*2^9*c.k,105178240164420+c.lower,105178623457826+c.upper)) = pointBounds29883 := by
 decide +kernel
def cuts29884 : List PrefixCut := [⟨61,201867838,201867953⟩,
⟨128,423976178,423976423⟩]
theorem checked29884 : checkPrefixCuts (2^48) 3920887809 9 Manual.Count131072.C029884.packed 128 cuts29884 = true := by
 decide +kernel
def pointBounds29884 : List (Nat × Nat × Nat) := [(3920950272,105178876503882,105179259797645)]
theorem point_links_checked29884 : (cuts29884.take 1).map (fun c => (3920887809-1+2*2^9*c.k,105178674636044+c.lower,105179057929692+c.upper)) = pointBounds29884 := by
 decide +kernel
def cuts29885 : List PrefixCut := [⟨53,174367391,174367490⟩,
⟨128,423674859,423675095⟩]
theorem checked29885 : checkPrefixCuts (2^48) 3921018881 9 Manual.Count131072.C029885.packed 128 cuts29885 = true := by
 decide +kernel
def pointBounds29885 : List (Nat × Nat × Nat) := [(3921073152,105179272979613,105179656273605)]
theorem point_links_checked29885 : (cuts29885.take 1).map (fun c => (3921018881-1+2*2^9*c.k,105179098612222+c.lower,105179481906115+c.upper)) = pointBounds29885 := by
 decide +kernel
def cuts29886 : List PrefixCut := [⟨45,151103929,151104013⟩,
⟨128,426532005,426532244⟩]
theorem checked29886 : checkPrefixCuts (2^48) 3921149953 9 Manual.Count131072.C029886.packed 128 cuts29886 = true := by
 decide +kernel
def pointBounds29886 : List (Nat × Nat × Nat) := [(3921196032,105179673391010,105180056685223)]
theorem point_links_checked29886 : (cuts29886.take 1).map (fun c => (3921149953-1+2*2^9*c.k,105179522287081+c.lower,105179905581210+c.upper)) = pointBounds29886 := by
 decide +kernel
def cuts29887 : List PrefixCut := [⟨37,120951018,120951083⟩,
⟨128,421205984,421206219⟩]
theorem checked29887 : checkPrefixCuts (2^48) 3921281025 9 Manual.Count131072.C029887.packed 128 cuts29887 = true := by
 decide +kernel
def pointBounds29887 : List (Nat × Nat × Nat) := [(3921318912,105180069770104,105180453064537)]
theorem point_links_checked29887 : (cuts29887.take 1).map (fun c => (3921281025-1+2*2^9*c.k,105179948819086+c.lower,105180332113454+c.upper)) = pointBounds29887 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000308
