import PlattAssemblyKernel
import PlattCertificates.Count131072.C043840
import PlattCertificates.Count131072.C043841
import PlattCertificates.Count131072.C043842
import PlattCertificates.Count131072.C043843
import PlattCertificates.Count131072.C043844
import PlattCertificates.Count131072.C043845
import PlattCertificates.Count131072.C043846
import PlattCertificates.Count131072.C043847
import PlattCertificates.Count131072.C043848
import PlattCertificates.Count131072.C043849
import PlattCertificates.Count131072.C043850
import PlattCertificates.Count131072.C043851
import PlattCertificates.Count131072.C043852
import PlattCertificates.Count131072.C043853
import PlattCertificates.Count131072.C043854
import PlattCertificates.Count131072.C043855
import PlattCertificates.Count131072.C043856
import PlattCertificates.Count131072.C043857
import PlattCertificates.Count131072.C043858
import PlattCertificates.Count131072.C043859
import PlattCertificates.Count131072.C043860
import PlattCertificates.Count131072.C043861
import PlattCertificates.Count131072.C043862
import PlattCertificates.Count131072.C043863
import PlattCertificates.Count131072.C043864
import PlattCertificates.Count131072.C043865
import PlattCertificates.Count131072.C043866
import PlattCertificates.Count131072.C043867
import PlattCertificates.Count131072.C043868
import PlattCertificates.Count131072.C043869
import PlattCertificates.Count131072.C043870
import PlattCertificates.Count131072.C043871
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000120
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts43840 : List PrefixCut := [⟨62,278773193,278773349⟩,
⟨64,287828936,287829097⟩]
theorem checked43840 : checkPrefixCuts (2^48) 5750128641 10 Manual.Count131072.C043840.packed 64 cuts43840 = true := by
 decide +kernel
def pointBounds43840 : List (Nat × Nat × Nat) := [(5750255616,110016246423313,110016632603775)]
theorem point_links_checked43840 : (cuts43840.take 1).map (fun c => (5750128641-1+2*2^10*c.k,110015967650120+c.lower,110016353830426+c.upper)) = pointBounds43840 := by
 decide +kernel
def cuts43841 : List PrefixCut := [⟨64,281556886,281557054⟩]
theorem checked43841 : checkPrefixCuts (2^48) 5750259713 10 Manual.Count131072.C043841.packed 64 cuts43841 = true := by
 decide +kernel
def cuts43842 : List PrefixCut := [⟨22,95988280,95988336⟩,
⟨64,282969948,282970117⟩]
theorem checked43842 : checkPrefixCuts (2^48) 5750390785 10 Manual.Count131072.C043842.packed 64 cuts43842 = true := by
 decide +kernel
def pointBounds43842 : List (Nat × Nat × Nat) := [(5750435840,110016633024222,110017019204913)]
theorem point_links_checked43842 : (cuts43842.take 1).map (fun c => (5750390785-1+2*2^10*c.k,110016537035942+c.lower,110016923216577+c.upper)) = pointBounds43842 := by
 decide +kernel
def cuts43843 : List PrefixCut := [⟨46,206019240,206019357⟩,
⟨64,286389805,286389969⟩]
theorem checked43843 : checkPrefixCuts (2^48) 5750521857 10 Manual.Count131072.C043843.packed 64 cuts43843 = true := by
 decide +kernel
def pointBounds43843 : List (Nat × Nat × Nat) := [(5750616064,110017026025130,110017412206051)]
theorem point_links_checked43843 : (cuts43843.take 1).map (fun c => (5750521857-1+2*2^10*c.k,110016820005890+c.lower,110017206186694+c.upper)) = pointBounds43843 := by
 decide +kernel
def cuts43844 : List PrefixCut := [⟨64,288439013,288439181⟩]
theorem checked43844 : checkPrefixCuts (2^48) 5750652929 10 Manual.Count131072.C043844.packed 64 cuts43844 = true := by
 decide +kernel
def cuts43845 : List PrefixCut := [⟨6,27605225,27605239⟩,
⟨64,285936258,285936424⟩]
theorem checked43845 : checkPrefixCuts (2^48) 5750784001 10 Manual.Count131072.C043845.packed 64 cuts43845 = true := by
 decide +kernel
def pointBounds43845 : List (Nat × Nat × Nat) := [(5750796288,110017422439933,110017808621083)]
theorem point_links_checked43845 : (cuts43845.take 1).map (fun c => (5750784001-1+2*2^10*c.k,110017394834708+c.lower,110017781015844+c.upper)) = pointBounds43845 := by
 decide +kernel
def cuts43846 : List PrefixCut := [⟨30,133372685,133372768⟩,
⟨64,283923046,283923215⟩]
theorem checked43846 : checkPrefixCuts (2^48) 5750915073 10 Manual.Count131072.C043846.packed 64 cuts43846 = true := by
 decide +kernel
def pointBounds43846 : List (Nat × Nat × Nat) := [(5750976512,110017814143651,110018200325036)]
theorem point_links_checked43846 : (cuts43846.take 1).map (fun c => (5750915073-1+2*2^10*c.k,110017680770966+c.lower,110018066952268+c.upper)) = pointBounds43846 := by
 decide +kernel
def cuts43847 : List PrefixCut := [⟨54,238547108,238547252⟩,
⟨64,284748569,284748738⟩]
theorem checked43847 : checkPrefixCuts (2^48) 5751046145 10 Manual.Count131072.C043847.packed 64 cuts43847 = true := by
 decide +kernel
def pointBounds43847 : List (Nat × Nat × Nat) := [(5751156736,110018203241120,110018589422735)]
theorem point_links_checked43847 : (cuts43847.take 1).map (fun c => (5751046145-1+2*2^10*c.k,110017964694012+c.lower,110018350875483+c.upper)) = pointBounds43847 := by
 decide +kernel
def cuts43848 : List PrefixCut := [⟨64,283812199,283812367⟩]
theorem checked43848 : checkPrefixCuts (2^48) 5751177217 10 Manual.Count131072.C043848.packed 64 cuts43848 = true := by
 decide +kernel
def cuts43849 : List PrefixCut := [⟨14,63525287,63525322⟩,
⟨64,284393048,284393215⟩]
theorem checked43849 : checkPrefixCuts (2^48) 5751308289 10 Manual.Count131072.C043849.packed 64 cuts43849 = true := by
 decide +kernel
def pointBounds43849 : List (Nat × Nat × Nat) := [(5751336960,110018596780067,110018982961910)]
theorem point_links_checked43849 : (cuts43849.take 1).map (fun c => (5751308289-1+2*2^10*c.k,110018533254780+c.lower,110018919436588+c.upper)) = pointBounds43849 := by
 decide +kernel
def cuts43850 : List PrefixCut := [⟨38,169967148,169967248⟩,
⟨64,288056998,288057161⟩]
theorem checked43850 : checkPrefixCuts (2^48) 5751439361 10 Manual.Count131072.C043850.packed 64 cuts43850 = true := by
 decide +kernel
def pointBounds43850 : List (Nat × Nat × Nat) := [(5751517184,110018987614976,110019373797051)]
theorem point_links_checked43850 : (cuts43850.take 1).map (fun c => (5751439361-1+2*2^10*c.k,110018817647828+c.lower,110019203829803+c.upper)) = pointBounds43850 := by
 decide +kernel
def cuts43851 : List PrefixCut := [⟨62,277430924,277431086⟩,
⟨64,286778023,286778191⟩]
theorem checked43851 : checkPrefixCuts (2^48) 5751570433 10 Manual.Count131072.C043851.packed 64 cuts43851 = true := by
 decide +kernel
def pointBounds43851 : List (Nat × Nat × Nat) := [(5751697408,110019383135750,110019769318050)]
theorem point_links_checked43851 : (cuts43851.take 1).map (fun c => (5751570433-1+2*2^10*c.k,110019105704826+c.lower,110019491886964+c.upper)) = pointBounds43851 := by
 decide +kernel
def cuts43852 : List PrefixCut := [⟨64,284275715,284275876⟩]
theorem checked43852 : checkPrefixCuts (2^48) 5751701505 10 Manual.Count131072.C043852.packed 64 cuts43852 = true := by
 decide +kernel
def cuts43853 : List PrefixCut := [⟨22,96600387,96600444⟩,
⟨64,283045830,283045999⟩]
theorem checked43853 : checkPrefixCuts (2^48) 5751832577 10 Manual.Count131072.C043853.packed 64 cuts43853 = true := by
 decide +kernel
def pointBounds43853 : List (Nat × Nat × Nat) := [(5751877632,110019773358951,110020159541475)]
theorem point_links_checked43853 : (cuts43853.take 1).map (fun c => (5751832577-1+2*2^10*c.k,110019676758564+c.lower,110020062941031+c.upper)) = pointBounds43853 := by
 decide +kernel
def cuts43854 : List PrefixCut := [⟨46,204499545,204499665⟩,
⟨64,285045708,285045875⟩]
theorem checked43854 : checkPrefixCuts (2^48) 5751963649 10 Manual.Count131072.C043854.packed 64 cuts43854 = true := by
 decide +kernel
def pointBounds43854 : List (Nat × Nat × Nat) := [(5752057856,110020164303939,110020550486695)]
theorem point_links_checked43854 : (cuts43854.take 1).map (fun c => (5751963649-1+2*2^10*c.k,110019959804394+c.lower,110020345987030+c.upper)) = pointBounds43854 := by
 decide +kernel
def cuts43855 : List PrefixCut := [⟨64,284452029,284452193⟩]
theorem checked43855 : checkPrefixCuts (2^48) 5752094721 10 Manual.Count131072.C043855.packed 64 cuts43855 = true := by
 decide +kernel
def cuts43856 : List PrefixCut := [⟨6,25200578,25200594⟩,
⟨64,286011398,286011563⟩]
theorem checked43856 : checkPrefixCuts (2^48) 5752225793 10 Manual.Count131072.C043856.packed 64 cuts43856 = true := by
 decide +kernel
def pointBounds43856 : List (Nat × Nat × Nat) := [(5752238080,110020554502709,110020940685692)]
theorem point_links_checked43856 : (cuts43856.take 1).map (fun c => (5752225793-1+2*2^10*c.k,110020529302131+c.lower,110020915485098+c.upper)) = pointBounds43856 := by
 decide +kernel
def cuts43857 : List PrefixCut := [⟨30,128054610,128054686⟩,
⟨64,277980058,277980223⟩]
theorem checked43857 : checkPrefixCuts (2^48) 5752356865 10 Manual.Count131072.C043857.packed 64 cuts43857 = true := by
 decide +kernel
def pointBounds43857 : List (Nat × Nat × Nat) := [(5752418304,110020943368139,110021329551347)]
theorem point_links_checked43857 : (cuts43857.take 1).map (fun c => (5752356865-1+2*2^10*c.k,110020815313529+c.lower,110021201496661+c.upper)) = pointBounds43857 := by
 decide +kernel
def cuts43858 : List PrefixCut := [⟨54,241961380,241961524⟩,
⟨64,287759819,287759990⟩]
theorem checked43858 : checkPrefixCuts (2^48) 5752487937 10 Manual.Count131072.C043858.packed 64 cuts43858 = true := by
 decide +kernel
def pointBounds43858 : List (Nat × Nat × Nat) := [(5752598528,110021335254967,110021721438408)]
theorem point_links_checked43858 : (cuts43858.take 1).map (fun c => (5752487937-1+2*2^10*c.k,110021093293587+c.lower,110021479476884+c.upper)) = pointBounds43858 := by
 decide +kernel
def cuts43859 : List PrefixCut := [⟨64,289906148,289906307⟩]
theorem checked43859 : checkPrefixCuts (2^48) 5752619009 10 Manual.Count131072.C043859.packed 64 cuts43859 = true := by
 decide +kernel
def cuts43860 : List PrefixCut := [⟨14,60133290,60133324⟩,
⟨64,281679622,281679789⟩]
theorem checked43860 : checkPrefixCuts (2^48) 5752750081 10 Manual.Count131072.C043860.packed 64 cuts43860 = true := by
 decide +kernel
def pointBounds43860 : List (Nat × Nat × Nat) := [(5752778752,110021731092844,110022117276505)]
theorem point_links_checked43860 : (cuts43860.take 1).map (fun c => (5752750081-1+2*2^10*c.k,110021670959554+c.lower,110022057143181+c.upper)) = pointBounds43860 := by
 decide +kernel
def cuts43861 : List PrefixCut := [⟨38,169924563,169924655⟩,
⟨64,288131591,288131756⟩]
theorem checked43861 : checkPrefixCuts (2^48) 5752881153 10 Manual.Count131072.C043861.packed 64 cuts43861 = true := by
 decide +kernel
def pointBounds43861 : List (Nat × Nat × Nat) := [(5752958976,110022122563739,110022508747625)]
theorem point_links_checked43861 : (cuts43861.take 1).map (fun c => (5752881153-1+2*2^10*c.k,110021952639176+c.lower,110022338822970+c.upper)) = pointBounds43861 := by
 decide +kernel
def cuts43862 : List PrefixCut := [⟨62,277508178,277508338⟩,
⟨64,286852935,286853100⟩]
theorem checked43862 : checkPrefixCuts (2^48) 5753012225 10 Manual.Count131072.C043862.packed 64 cuts43862 = true := by
 decide +kernel
def pointBounds43862 : List (Nat × Nat × Nat) := [(5753139200,110022518278945,110022904463064)]
theorem point_links_checked43862 : (cuts43862.take 1).map (fun c => (5753012225-1+2*2^10*c.k,110022240770767+c.lower,110022626954726+c.upper)) = pointBounds43862 := by
 decide +kernel
def cuts43863 : List PrefixCut := [⟨64,284987255,284987415⟩]
theorem checked43863 : checkPrefixCuts (2^48) 5753143297 10 Manual.Count131072.C043863.packed 64 cuts43863 = true := by
 decide +kernel
def cuts43864 : List PrefixCut := [⟨22,98533140,98533200⟩,
⟨64,286986637,286986801⟩]
theorem checked43864 : checkPrefixCuts (2^48) 5753274369 10 Manual.Count131072.C043864.packed 64 cuts43864 = true := by
 decide +kernel
def pointBounds43864 : List (Nat × Nat × Nat) := [(5753319424,110022911144097,110023297328441)]
theorem point_links_checked43864 : (cuts43864.take 1).map (fun c => (5753274369-1+2*2^10*c.k,110022812610957+c.lower,110023198795241+c.upper)) = pointBounds43864 := by
 decide +kernel
def cuts43865 : List PrefixCut := [⟨46,207041215,207041334⟩,
⟨64,288154260,288154426⟩]
theorem checked43865 : checkPrefixCuts (2^48) 5753405441 10 Manual.Count131072.C043865.packed 64 cuts43865 = true := by
 decide +kernel
def pointBounds43865 : List (Nat × Nat × Nat) := [(5753499648,110023306638809,110023692823376)]
theorem point_links_checked43865 : (cuts43865.take 1).map (fun c => (5753405441-1+2*2^10*c.k,110023099597594+c.lower,110023485782042+c.upper)) = pointBounds43865 := by
 decide +kernel
def cuts43866 : List PrefixCut := [⟨64,291180839,291181000⟩]
theorem checked43866 : checkPrefixCuts (2^48) 5753536513 10 Manual.Count131072.C043866.packed 64 cuts43866 = true := by
 decide +kernel
def cuts43867 : List PrefixCut := [⟨6,25683471,25683487⟩,
⟨64,283640438,283640606⟩]
theorem checked43867 : checkPrefixCuts (2^48) 5753667585 10 Manual.Count131072.C043867.packed 64 cuts43867 = true := by
 decide +kernel
def pointBounds43867 : List (Nat × Nat × Nat) := [(5753679872,110023704616164,110024090800955)]
theorem point_links_checked43867 : (cuts43867.take 1).map (fun c => (5753667585-1+2*2^10*c.k,110023678932693+c.lower,110024065117468+c.upper)) = pointBounds43867 := by
 decide +kernel
def cuts43868 : List PrefixCut := [⟨30,135898583,135898661⟩,
⟨64,284759165,284759330⟩]
theorem checked43868 : checkPrefixCuts (2^48) 5753798657 10 Manual.Count131072.C043868.packed 64 cuts43868 = true := by
 decide +kernel
def pointBounds43868 : List (Nat × Nat × Nat) := [(5753860096,110024098471714,110024484656735)]
theorem point_links_checked43868 : (cuts43868.take 1).map (fun c => (5753798657-1+2*2^10*c.k,110023962573131+c.lower,110024348758074+c.upper)) = pointBounds43868 := by
 decide +kernel
def cuts43869 : List PrefixCut := [⟨54,239014587,239014722⟩,
⟨64,284067787,284067945⟩]
theorem checked43869 : checkPrefixCuts (2^48) 5753929729 10 Manual.Count131072.C043869.packed 64 cuts43869 = true := by
 decide +kernel
def pointBounds43869 : List (Nat × Nat × Nat) := [(5754040320,110024486346883,110024872532126)]
theorem point_links_checked43869 : (cuts43869.take 1).map (fun c => (5753929729-1+2*2^10*c.k,110024247332296+c.lower,110024633517404+c.upper)) = pointBounds43869 := by
 decide +kernel
def cuts43870 : List PrefixCut := [⟨64,288855195,288855358⟩]
theorem checked43870 : checkPrefixCuts (2^48) 5754060801 10 Manual.Count131072.C043870.packed 64 cuts43870 = true := by
 decide +kernel
def cuts43871 : List PrefixCut := [⟨14,59482313,59482346⟩,
⟨64,282978662,282978824⟩]
theorem checked43871 : checkPrefixCuts (2^48) 5754191873 10 Manual.Count131072.C043871.packed 64 cuts43871 = true := by
 decide +kernel
def pointBounds43871 : List (Nat × Nat × Nat) := [(5754220544,110024879737591,110025265923053)]
theorem point_links_checked43871 : (cuts43871.take 1).map (fun c => (5754191873-1+2*2^10*c.k,110024820255278+c.lower,110025206440707+c.upper)) = pointBounds43871 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000120
