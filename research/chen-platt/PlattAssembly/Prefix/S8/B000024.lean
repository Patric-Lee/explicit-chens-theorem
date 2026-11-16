import PlattAssemblyKernel
import PlattCertificates.Count131072.C070768
import PlattCertificates.Count131072.C070769
import PlattCertificates.Count131072.C070770
import PlattCertificates.Count131072.C070771
import PlattCertificates.Count131072.C070772
import PlattCertificates.Count131072.C070773
import PlattCertificates.Count131072.C070774
import PlattCertificates.Count131072.C070775
import PlattCertificates.Count131072.C070776
import PlattCertificates.Count131072.C070777
import PlattCertificates.Count131072.C070778
import PlattCertificates.Count131072.C070779
import PlattCertificates.Count131072.C070780
import PlattCertificates.Count131072.C070781
import PlattCertificates.Count131072.C070782
import PlattCertificates.Count131072.C070783
import PlattCertificates.Count131072.C070784
import PlattCertificates.Count131072.C070785
import PlattCertificates.Count131072.C070786
import PlattCertificates.Count131072.C070787
import PlattCertificates.Count131072.C070788
import PlattCertificates.Count131072.C070789
import PlattCertificates.Count131072.C070790
import PlattCertificates.Count131072.C070791
import PlattCertificates.Count131072.C070792
import PlattCertificates.Count131072.C070793
import PlattCertificates.Count131072.C070794
import PlattCertificates.Count131072.C070795
import PlattCertificates.Count131072.C070796
import PlattCertificates.Count131072.C070797
import PlattCertificates.Count131072.C070798
import PlattCertificates.Count131072.C070799
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000024
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70768 : List PrefixCut := [⟨21,56600384,56600415⟩,
⟨64,173227901,173227997⟩]
theorem checked70768 : checkPrefixCuts (2^48) 9279635457 10 Manual.Count131072.C070768.packed 64 cuts70768 = true := by
 decide +kernel
def pointBounds70768 : List (Nat × Nat × Nat) := [(9279678464,115947617876319,115948007460364)]
theorem point_links_checked70768 : (cuts70768.take 1).map (fun c => (9279635457-1+2*2^10*c.k,115947561275935+c.lower,115947950859949+c.upper)) = pointBounds70768 := by
 decide +kernel
def cuts70769 : List PrefixCut := [⟨64,172831136,172831238⟩]
theorem checked70769 : checkPrefixCuts (2^48) 9279766529 10 Manual.Count131072.C070769.packed 64 cuts70769 = true := by
 decide +kernel
def cuts70770 : List PrefixCut := [⟨35,95726419,95726474⟩,
⟨64,174496933,174497039⟩]
theorem checked70770 : checkPrefixCuts (2^48) 9279897601 10 Manual.Count131072.C070770.packed 64 cuts70770 = true := by
 decide +kernel
def pointBounds70770 : List (Nat × Nat × Nat) := [(9279969280,115948003061391,115948392645658)]
theorem point_links_checked70770 : (cuts70770.take 1).map (fun c => (9279897601-1+2*2^10*c.k,115947907334972+c.lower,115948296919184+c.upper)) = pointBounds70770 := by
 decide +kernel
def cuts70771 : List PrefixCut := [⟨64,175768368,175768476⟩]
theorem checked70771 : checkPrefixCuts (2^48) 9280028673 10 Manual.Count131072.C070771.packed 64 cuts70771 = true := by
 decide +kernel
def cuts70772 : List PrefixCut := [⟨49,130785807,130785883⟩,
⟨64,171155631,171155734⟩]
theorem checked70772 : checkPrefixCuts (2^48) 9280159745 10 Manual.Count131072.C070772.packed 64 cuts70772 = true := by
 decide +kernel
def pointBounds70772 : List (Nat × Nat × Nat) := [(9280260096,115948388386080,115948777970582)]
theorem point_links_checked70772 : (cuts70772.take 1).map (fun c => (9280159745-1+2*2^10*c.k,115948257600273+c.lower,115948647184699+c.upper)) = pointBounds70772 := by
 decide +kernel
def cuts70773 : List PrefixCut := [⟨64,170849901,170850007⟩]
theorem checked70773 : checkPrefixCuts (2^48) 9280290817 10 Manual.Count131072.C070773.packed 64 cuts70773 = true := by
 decide +kernel
def cuts70774 : List PrefixCut := [⟨63,170240929,170241023⟩,
⟨64,172606633,172606729⟩]
theorem checked70774 : checkPrefixCuts (2^48) 9280421889 10 Manual.Count131072.C070774.packed 64 cuts70774 = true := by
 decide +kernel
def pointBounds70774 : List (Nat × Nat × Nat) := [(9280550912,115948769846734,115949159431463)]
theorem point_links_checked70774 : (cuts70774.take 1).map (fun c => (9280421889-1+2*2^10*c.k,115948599605805+c.lower,115948989190440+c.upper)) = pointBounds70774 := by
 decide +kernel
def cuts70775 : List PrefixCut := [⟨64,173847698,173847802⟩]
theorem checked70775 : checkPrefixCuts (2^48) 9280552961 10 Manual.Count131072.C070775.packed 64 cuts70775 = true := by
 decide +kernel
def cuts70776 : List PrefixCut := [⟨64,170873001,170873097⟩]
theorem checked70776 : checkPrefixCuts (2^48) 9280684033 10 Manual.Count131072.C070776.packed 64 cuts70776 = true := by
 decide +kernel
def cuts70777 : List PrefixCut := [⟨13,34817280,34817296⟩,
⟨64,173903433,173903536⟩]
theorem checked70777 : checkPrefixCuts (2^48) 9280815105 10 Manual.Count131072.C070777.packed 64 cuts70777 = true := by
 decide +kernel
def pointBounds70777 : List (Nat × Nat × Nat) := [(9280841728,115949151750417,115949541335364)]
theorem point_links_checked70777 : (cuts70777.take 1).map (fun c => (9280815105-1+2*2^10*c.k,115949116933137+c.lower,115949506518068+c.upper)) = pointBounds70777 := by
 decide +kernel
def cuts70778 : List PrefixCut := [⟨64,174659185,174659292⟩]
theorem checked70778 : checkPrefixCuts (2^48) 9280946177 10 Manual.Count131072.C070778.packed 64 cuts70778 = true := by
 decide +kernel
def cuts70779 : List PrefixCut := [⟨27,71816076,71816118⟩,
⟨64,173534587,173534687⟩]
theorem checked70779 : checkPrefixCuts (2^48) 9281077249 10 Manual.Count131072.C070779.packed 64 cuts70779 = true := by
 decide +kernel
def pointBounds70779 : List (Nat × Nat × Nat) := [(9281132544,115949537311831,115949926897014)]
theorem point_links_checked70779 : (cuts70779.take 1).map (fun c => (9281077249-1+2*2^10*c.k,115949465495755+c.lower,115949855080896+c.upper)) = pointBounds70779 := by
 decide +kernel
def cuts70780 : List PrefixCut := [⟨64,172106769,172106868⟩]
theorem checked70780 : checkPrefixCuts (2^48) 9281208321 10 Manual.Count131072.C070780.packed 64 cuts70780 = true := by
 decide +kernel
def cuts70781 : List PrefixCut := [⟨41,111481435,111481502⟩,
⟨64,173984595,173984698⟩]
theorem checked70781 : checkPrefixCuts (2^48) 9281339393 10 Manual.Count131072.C070781.packed 64 cuts70781 = true := by
 decide +kernel
def pointBounds70781 : List (Nat × Nat × Nat) := [(9281423360,115949922618546,115950312203953)]
theorem point_links_checked70781 : (cuts70781.take 1).map (fun c => (9281339393-1+2*2^10*c.k,115949811137111+c.lower,115950200722451+c.upper)) = pointBounds70781 := by
 decide +kernel
def cuts70782 : List PrefixCut := [⟨64,174497700,174497794⟩]
theorem checked70782 : checkPrefixCuts (2^48) 9281470465 10 Manual.Count131072.C070782.packed 64 cuts70782 = true := by
 decide +kernel
def cuts70783 : List PrefixCut := [⟨55,148354451,148354536⟩,
⟨64,172615023,172615121⟩]
theorem checked70783 : checkPrefixCuts (2^48) 9281601537 10 Manual.Count131072.C070783.packed 64 cuts70783 = true := by
 decide +kernel
def pointBounds70783 : List (Nat × Nat × Nat) := [(9281714176,115950307973857,115950697559479)]
theorem point_links_checked70783 : (cuts70783.take 1).map (fun c => (9281601537-1+2*2^10*c.k,115950159619406+c.lower,115950549204943+c.upper)) = pointBounds70783 := by
 decide +kernel
def cuts70784 : List PrefixCut := [⟨64,173310065,173310162⟩]
theorem checked70784 : checkPrefixCuts (2^48) 9281732609 10 Manual.Count131072.C070784.packed 64 cuts70784 = true := by
 decide +kernel
def cuts70785 : List PrefixCut := [⟨64,171882340,171882441⟩]
theorem checked70785 : checkPrefixCuts (2^48) 9281863681 10 Manual.Count131072.C070785.packed 64 cuts70785 = true := by
 decide +kernel
def cuts70786 : List PrefixCut := [⟨5,14131361,14131370⟩,
⟨64,176792491,176792597⟩]
theorem checked70786 : checkPrefixCuts (2^48) 9281994753 10 Manual.Count131072.C070786.packed 64 cuts70786 = true := by
 decide +kernel
def pointBounds70786 : List (Nat × Nat × Nat) := [(9282004992,115950691558195,115951081144037)]
theorem point_links_checked70786 : (cuts70786.take 1).map (fun c => (9281994753-1+2*2^10*c.k,115950677426834+c.lower,115951067012667+c.upper)) = pointBounds70786 := by
 decide +kernel
def cuts70787 : List PrefixCut := [⟨64,172180721,172180823⟩]
theorem checked70787 : checkPrefixCuts (2^48) 9282125825 10 Manual.Count131072.C070787.packed 64 cuts70787 = true := by
 decide +kernel
def cuts70788 : List PrefixCut := [⟨19,51277727,51277760⟩,
⟨64,173451889,173451998⟩]
theorem checked70788 : checkPrefixCuts (2^48) 9282256897 10 Manual.Count131072.C070788.packed 64 cuts70788 = true := by
 decide +kernel
def pointBounds70788 : List (Nat × Nat × Nat) := [(9282295808,115951077677773,115951467263847)]
theorem point_links_checked70788 : (cuts70788.take 1).map (fun c => (9282256897-1+2*2^10*c.k,115951026400046+c.lower,115951415986087+c.upper)) = pointBounds70788 := by
 decide +kernel
def cuts70789 : List PrefixCut := [⟨64,174389464,174389560⟩]
theorem checked70789 : checkPrefixCuts (2^48) 9282387969 10 Manual.Count131072.C070789.packed 64 cuts70789 = true := by
 decide +kernel
def cuts70790 : List PrefixCut := [⟨33,90029001,90029053⟩,
⟨64,173113443,173113545⟩]
theorem checked70790 : checkPrefixCuts (2^48) 9282519041 10 Manual.Count131072.C070790.packed 64 cuts70790 = true := by
 decide +kernel
def pointBounds70790 : List (Nat × Nat × Nat) := [(9282586624,115951464270400,115951853856698)]
theorem point_links_checked70790 : (cuts70790.take 1).map (fun c => (9282519041-1+2*2^10*c.k,115951374241399+c.lower,115951763827645+c.upper)) = pointBounds70790 := by
 decide +kernel
def cuts70791 : List PrefixCut := [⟨64,174172289,174172397⟩]
theorem checked70791 : checkPrefixCuts (2^48) 9282650113 10 Manual.Count131072.C070791.packed 64 cuts70791 = true := by
 decide +kernel
def cuts70792 : List PrefixCut := [⟨47,127716698,127716772⟩,
⟨64,171865365,171865467⟩]
theorem checked70792 : checkPrefixCuts (2^48) 9282781185 10 Manual.Count131072.C070792.packed 64 cuts70792 = true := by
 decide +kernel
def pointBounds70792 : List (Nat × Nat × Nat) := [(9282877440,115951849243829,115952238830359)]
theorem point_links_checked70792 : (cuts70792.take 1).map (fun c => (9282781185-1+2*2^10*c.k,115951721527131+c.lower,115952111113587+c.upper)) = pointBounds70792 := by
 decide +kernel
def cuts70793 : List PrefixCut := [⟨64,173106113,173106218⟩]
theorem checked70793 : checkPrefixCuts (2^48) 9282912257 10 Manual.Count131072.C070793.packed 64 cuts70793 = true := by
 decide +kernel
def cuts70794 : List PrefixCut := [⟨61,165250533,165250635⟩,
⟨64,173012705,173012812⟩]
theorem checked70794 : checkPrefixCuts (2^48) 9283043329 10 Manual.Count131072.C070794.packed 64 cuts70794 = true := by
 decide +kernel
def pointBounds70794 : List (Nat × Nat × Nat) := [(9283168256,115952231749142,115952621335907)]
theorem point_links_checked70794 : (cuts70794.take 1).map (fun c => (9283043329-1+2*2^10*c.k,115952066498609+c.lower,115952456085272+c.upper)) = pointBounds70794 := by
 decide +kernel
def cuts70795 : List PrefixCut := [⟨64,174435339,174435437⟩]
theorem checked70795 : checkPrefixCuts (2^48) 9283174401 10 Manual.Count131072.C070795.packed 64 cuts70795 = true := by
 decide +kernel
def cuts70796 : List PrefixCut := [⟨64,171249236,171249335⟩]
theorem checked70796 : checkPrefixCuts (2^48) 9283305473 10 Manual.Count131072.C070796.packed 64 cuts70796 = true := by
 decide +kernel
def cuts70797 : List PrefixCut := [⟨11,29167919,29167934⟩,
⟨64,172065453,172065547⟩]
theorem checked70797 : checkPrefixCuts (2^48) 9283436545 10 Manual.Count131072.C070797.packed 64 cuts70797 = true := by
 decide +kernel
def pointBounds70797 : List (Nat × Nat × Nat) := [(9283459072,115952614363808,115953003950790)]
theorem point_links_checked70797 : (cuts70797.take 1).map (fun c => (9283436545-1+2*2^10*c.k,115952585195889+c.lower,115952974782856+c.upper)) = pointBounds70797 := by
 decide +kernel
def cuts70798 : List PrefixCut := [⟨64,173427405,173427503⟩]
theorem checked70798 : checkPrefixCuts (2^48) 9283567617 10 Manual.Count131072.C070798.packed 64 cuts70798 = true := by
 decide +kernel
def cuts70799 : List PrefixCut := [⟨25,65853255,65853292⟩,
⟨64,171878678,171878778⟩]
theorem checked70799 : checkPrefixCuts (2^48) 9283698689 10 Manual.Count131072.C070799.packed 64 cuts70799 = true := by
 decide +kernel
def pointBounds70799 : List (Nat × Nat × Nat) := [(9283749888,115952996542002,115953386129198)]
theorem point_links_checked70799 : (cuts70799.take 1).map (fun c => (9283698689-1+2*2^10*c.k,115952930688747+c.lower,115953320275906+c.upper)) = pointBounds70799 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000024
