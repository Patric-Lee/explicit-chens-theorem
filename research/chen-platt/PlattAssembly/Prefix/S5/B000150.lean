import PlattAssemblyKernel
import PlattCertificates.Count131072.C044800
import PlattCertificates.Count131072.C044801
import PlattCertificates.Count131072.C044802
import PlattCertificates.Count131072.C044803
import PlattCertificates.Count131072.C044804
import PlattCertificates.Count131072.C044805
import PlattCertificates.Count131072.C044806
import PlattCertificates.Count131072.C044807
import PlattCertificates.Count131072.C044808
import PlattCertificates.Count131072.C044809
import PlattCertificates.Count131072.C044810
import PlattCertificates.Count131072.C044811
import PlattCertificates.Count131072.C044812
import PlattCertificates.Count131072.C044813
import PlattCertificates.Count131072.C044814
import PlattCertificates.Count131072.C044815
import PlattCertificates.Count131072.C044816
import PlattCertificates.Count131072.C044817
import PlattCertificates.Count131072.C044818
import PlattCertificates.Count131072.C044819
import PlattCertificates.Count131072.C044820
import PlattCertificates.Count131072.C044821
import PlattCertificates.Count131072.C044822
import PlattCertificates.Count131072.C044823
import PlattCertificates.Count131072.C044824
import PlattCertificates.Count131072.C044825
import PlattCertificates.Count131072.C044826
import PlattCertificates.Count131072.C044827
import PlattCertificates.Count131072.C044828
import PlattCertificates.Count131072.C044829
import PlattCertificates.Count131072.C044830
import PlattCertificates.Count131072.C044831
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000150
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts44800 : List PrefixCut := [⟨64,275198597,275198759⟩]
theorem checked44800 : checkPrefixCuts (2^48) 5875957761 10 Manual.Count131072.C044800.packed 64 cuts44800 = true := by
 decide +kernel
def cuts44801 : List PrefixCut := [⟨19,81624297,81624346⟩,
⟨64,280461539,280461704⟩]
theorem checked44801 : checkPrefixCuts (2^48) 5876088833 10 Manual.Count131072.C044801.packed 64 cuts44801 = true := by
 decide +kernel
def pointBounds44801 : List (Nat × Nat × Nat) := [(5876127744,110287302368832,110287688706227)]
theorem point_links_checked44801 : (cuts44801.take 1).map (fun c => (5876088833-1+2*2^10*c.k,110287220744535+c.lower,110287607081881+c.upper)) = pointBounds44801 := by
 decide +kernel
def cuts44802 : List PrefixCut := [⟨45,196678609,196678724⟩,
⟨64,279257799,279257965⟩]
theorem checked44802 : checkPrefixCuts (2^48) 5876219905 10 Manual.Count131072.C044802.packed 64 cuts44802 = true := by
 decide +kernel
def pointBounds44802 : List (Nat × Nat × Nat) := [(5876312064,110287697884683,110288084222309)]
theorem point_links_checked44802 : (cuts44802.take 1).map (fun c => (5876219905-1+2*2^10*c.k,110287501206074+c.lower,110287887543585+c.upper)) = pointBounds44802 := by
 decide +kernel
def cuts44803 : List PrefixCut := [⟨64,283227213,283227377⟩]
theorem checked44803 : checkPrefixCuts (2^48) 5876350977 10 Manual.Count131072.C044803.packed 64 cuts44803 = true := by
 decide +kernel
def cuts44804 : List PrefixCut := [⟨7,28499594,28499611⟩,
⟨64,277712593,277712753⟩]
theorem checked44804 : checkPrefixCuts (2^48) 5876482049 10 Manual.Count131072.C044804.packed 64 cuts44804 = true := by
 decide +kernel
def pointBounds44804 : List (Nat × Nat × Nat) := [(5876496384,110288092190680,110288478528538)]
theorem point_links_checked44804 : (cuts44804.take 1).map (fun c => (5876482049-1+2*2^10*c.k,110288063691086+c.lower,110288450028927+c.upper)) = pointBounds44804 := by
 decide +kernel
def cuts44805 : List PrefixCut := [⟨33,143643684,143643766⟩,
⟨64,278089610,278089768⟩]
theorem checked44805 : checkPrefixCuts (2^48) 5876613121 10 Manual.Count131072.C044805.packed 64 cuts44805 = true := by
 decide +kernel
def pointBounds44805 : List (Nat × Nat × Nat) := [(5876680704,110288485047363,110288871385446)]
theorem point_links_checked44805 : (cuts44805.take 1).map (fun c => (5876613121-1+2*2^10*c.k,110288341403679+c.lower,110288727741680+c.upper)) = pointBounds44805 := by
 decide +kernel
def cuts44806 : List PrefixCut := [⟨59,260362156,260362311⟩,
⟨64,282968774,282968940⟩]
theorem checked44806 : checkPrefixCuts (2^48) 5876744193 10 Manual.Count131072.C044806.packed 64 cuts44806 = true := by
 decide +kernel
def pointBounds44806 : List (Nat × Nat × Nat) := [(5876865024,110288879855445,110289266193759)]
theorem point_links_checked44806 : (cuts44806.take 1).map (fun c => (5876744193-1+2*2^10*c.k,110288619493289+c.lower,110289005831448+c.upper)) = pointBounds44806 := by
 decide +kernel
def cuts44807 : List PrefixCut := [⟨64,275874041,275874203⟩]
theorem checked44807 : checkPrefixCuts (2^48) 5876875265 10 Manual.Count131072.C044807.packed 64 cuts44807 = true := by
 decide +kernel
def cuts44808 : List PrefixCut := [⟨21,92818753,92818803⟩,
⟨64,279076782,279076939⟩]
theorem checked44808 : checkPrefixCuts (2^48) 5877006337 10 Manual.Count131072.C044808.packed 64 cuts44808 = true := by
 decide +kernel
def pointBounds44808 : List (Nat × Nat × Nat) := [(5877049344,110289271154857,110289657493394)]
theorem point_links_checked44808 : (cuts44808.take 1).map (fun c => (5877006337-1+2*2^10*c.k,110289178336104+c.lower,110289564674591+c.upper)) = pointBounds44808 := by
 decide +kernel
def cuts44809 : List PrefixCut := [⟨47,204645972,204646091⟩,
⟨64,279022668,279022829⟩]
theorem checked44809 : checkPrefixCuts (2^48) 5877137409 10 Manual.Count131072.C044809.packed 64 cuts44809 = true := by
 decide +kernel
def pointBounds44809 : List (Nat × Nat × Nat) := [(5877233664,110289662058858,110290048397621)]
theorem point_links_checked44809 : (cuts44809.take 1).map (fun c => (5877137409-1+2*2^10*c.k,110289457412886+c.lower,110289843751530+c.upper)) = pointBounds44809 := by
 decide +kernel
def cuts44810 : List PrefixCut := [⟨64,277531783,277531948⟩]
theorem checked44810 : checkPrefixCuts (2^48) 5877268481 10 Manual.Count131072.C044810.packed 64 cuts44810 = true := by
 decide +kernel
def cuts44811 : List PrefixCut := [⟨9,39941082,39941106⟩,
⟨64,282745667,282745832⟩]
theorem checked44811 : checkPrefixCuts (2^48) 5877399553 10 Manual.Count131072.C044811.packed 64 cuts44811 = true := by
 decide +kernel
def pointBounds44811 : List (Nat × Nat × Nat) := [(5877417984,110290053908419,110290440247413)]
theorem point_links_checked44811 : (cuts44811.take 1).map (fun c => (5877399553-1+2*2^10*c.k,110290013967337+c.lower,110290400306307+c.upper)) = pointBounds44811 := by
 decide +kernel
def cuts44812 : List PrefixCut := [⟨35,146590360,146590444⟩,
⟨64,275220665,275220823⟩]
theorem checked44812 : checkPrefixCuts (2^48) 5877530625 10 Manual.Count131072.C044812.packed 64 cuts44812 = true := by
 decide +kernel
def pointBounds44812 : List (Nat × Nat × Nat) := [(5877602304,110290443303364,110290829642583)]
theorem point_links_checked44812 : (cuts44812.take 1).map (fun c => (5877530625-1+2*2^10*c.k,110290296713004+c.lower,110290683052139+c.upper)) = pointBounds44812 := by
 decide +kernel
def cuts44813 : List PrefixCut := [⟨61,265924371,265924521⟩,
⟨64,277609014,277609171⟩]
theorem checked44813 : checkPrefixCuts (2^48) 5877661697 10 Manual.Count131072.C044813.packed 64 cuts44813 = true := by
 decide +kernel
def pointBounds44813 : List (Nat × Nat × Nat) := [(5877786624,110290837858040,110291224197483)]
theorem point_links_checked44813 : (cuts44813.take 1).map (fun c => (5877661697-1+2*2^10*c.k,110290571933669+c.lower,110290958272962+c.upper)) = pointBounds44813 := by
 decide +kernel
def cuts44814 : List PrefixCut := [⟨64,281433805,281433962⟩]
theorem checked44814 : checkPrefixCuts (2^48) 5877792769 10 Manual.Count131072.C044814.packed 64 cuts44814 = true := by
 decide +kernel
def cuts44815 : List PrefixCut := [⟨23,98406951,98407009⟩,
⟨64,279847235,279847397⟩]
theorem checked44815 : checkPrefixCuts (2^48) 5877923841 10 Manual.Count131072.C044815.packed 64 cuts44815 = true := by
 decide +kernel
def pointBounds44815 : List (Nat × Nat × Nat) := [(5877970944,110291229383439,110291615723104)]
theorem point_links_checked44815 : (cuts44815.take 1).map (fun c => (5877923841-1+2*2^10*c.k,110291130976488+c.lower,110291517316095+c.upper)) = pointBounds44815 := by
 decide +kernel
def cuts44816 : List PrefixCut := [⟨49,210982680,210982806⟩,
⟨64,275531363,275531527⟩]
theorem checked44816 : checkPrefixCuts (2^48) 5878054913 10 Manual.Count131072.C044816.packed 64 cuts44816 = true := by
 decide +kernel
def pointBounds44816 : List (Nat × Nat × Nat) := [(5878155264,110291621806403,110292008146298)]
theorem point_links_checked44816 : (cuts44816.take 1).map (fun c => (5878054913-1+2*2^10*c.k,110291410823723+c.lower,110291797163492+c.upper)) = pointBounds44816 := by
 decide +kernel
def cuts44817 : List PrefixCut := [⟨64,275477343,275477503⟩]
theorem checked44817 : checkPrefixCuts (2^48) 5878185985 10 Manual.Count131072.C044817.packed 64 cuts44817 = true := by
 decide +kernel
def cuts44818 : List PrefixCut := [⟨11,48553863,48553889⟩,
⟨64,280834096,280834255⟩]
theorem checked44818 : checkPrefixCuts (2^48) 5878317057 10 Manual.Count131072.C044818.packed 64 cuts44818 = true := by
 decide +kernel
def pointBounds44818 : List (Nat × Nat × Nat) := [(5878339584,110292010386292,110292396726411)]
theorem point_links_checked44818 : (cuts44818.take 1).map (fun c => (5878317057-1+2*2^10*c.k,110291961832429+c.lower,110292348172522+c.upper)) = pointBounds44818 := by
 decide +kernel
def cuts44819 : List PrefixCut := [⟨37,158729524,158729616⟩,
⟨64,275608688,275608850⟩]
theorem checked44819 : checkPrefixCuts (2^48) 5878448129 10 Manual.Count131072.C044819.packed 64 cuts44819 = true := by
 decide +kernel
def pointBounds44819 : List (Nat × Nat × Nat) := [(5878523904,110292401396049,110292787736393)]
theorem point_links_checked44819 : (cuts44819.take 1).map (fun c => (5878448129-1+2*2^10*c.k,110292242666525+c.lower,110292629006777+c.upper)) = pointBounds44819 := by
 decide +kernel
def cuts44820 : List PrefixCut := [⟨63,273735249,273735409⟩,
⟨64,278810570,278810733⟩]
theorem checked44820 : checkPrefixCuts (2^48) 5878579201 10 Manual.Count131072.C044820.packed 64 cuts44820 = true := by
 decide +kernel
def pointBounds44820 : List (Nat × Nat × Nat) := [(5878708224,110292792010462,110293178351036)]
theorem point_links_checked44820 : (cuts44820.take 1).map (fun c => (5878579201-1+2*2^10*c.k,110292518275213+c.lower,110292904615627+c.upper)) = pointBounds44820 := by
 decide +kernel
def cuts44821 : List PrefixCut := [⟨64,281294117,281294273⟩]
theorem checked44821 : checkPrefixCuts (2^48) 5878710273 10 Manual.Count131072.C044821.packed 64 cuts44821 = true := by
 decide +kernel
def cuts44822 : List PrefixCut := [⟨25,109260123,109260189⟩,
⟨64,281239957,281240119⟩]
theorem checked44822 : checkPrefixCuts (2^48) 5878841345 10 Manual.Count131072.C044822.packed 64 cuts44822 = true := by
 decide +kernel
def pointBounds44822 : List (Nat × Nat × Nat) := [(5878892544,110293187640023,110293573980822)]
theorem point_links_checked44822 : (cuts44822.take 1).map (fun c => (5878841345-1+2*2^10*c.k,110293078379900+c.lower,110293464720633+c.upper)) = pointBounds44822 := by
 decide +kernel
def cuts44823 : List PrefixCut := [⟨51,223014903,223015026⟩,
⟨64,278600440,278600594⟩]
theorem checked44823 : checkPrefixCuts (2^48) 5878972417 10 Manual.Count131072.C044823.packed 64 cuts44823 = true := by
 decide +kernel
def pointBounds44823 : List (Nat × Nat × Nat) := [(5879076864,110293582634760,110293968975778)]
theorem point_links_checked44823 : (cuts44823.take 1).map (fun c => (5878972417-1+2*2^10*c.k,110293359619857+c.lower,110293745960752+c.upper)) = pointBounds44823 := by
 decide +kernel
def cuts44824 : List PrefixCut := [⟨64,279551764,279551928⟩]
theorem checked44824 : checkPrefixCuts (2^48) 5879103489 10 Manual.Count131072.C044824.packed 64 cuts44824 = true := by
 decide +kernel
def cuts44825 : List PrefixCut := [⟨13,54913777,54913809⟩,
⟨64,277678354,277678516⟩]
theorem checked44825 : checkPrefixCuts (2^48) 5879234561 10 Manual.Count131072.C044825.packed 64 cuts44825 = true := by
 decide +kernel
def pointBounds44825 : List (Nat × Nat × Nat) := [(5879261184,110293972685838,110294359027083)]
theorem point_links_checked44825 : (cuts44825.take 1).map (fun c => (5879234561-1+2*2^10*c.k,110293917772061+c.lower,110294304113274+c.upper)) = pointBounds44825 := by
 decide +kernel
def cuts44826 : List PrefixCut := [⟨39,170912742,170912843⟩,
⟨64,279826515,279826678⟩]
theorem checked44826 : checkPrefixCuts (2^48) 5879365633 10 Manual.Count131072.C044826.packed 64 cuts44826 = true := by
 decide +kernel
def pointBounds44826 : List (Nat × Nat × Nat) := [(5879445504,110294366363157,110294752704633)]
theorem point_links_checked44826 : (cuts44826.take 1).map (fun c => (5879365633-1+2*2^10*c.k,110294195450415+c.lower,110294581791790+c.upper)) = pointBounds44826 := by
 decide +kernel
def cuts44827 : List PrefixCut := [⟨64,281017126,281017281⟩]
theorem checked44827 : checkPrefixCuts (2^48) 5879496705 10 Manual.Count131072.C044827.packed 64 cuts44827 = true := by
 decide +kernel
def cuts44828 : List PrefixCut := [⟨1,4356434,4356437⟩,
⟨64,281681051,281681213⟩]
theorem checked44828 : checkPrefixCuts (2^48) 5879627777 10 Manual.Count131072.C044828.packed 64 cuts44828 = true := by
 decide +kernel
def pointBounds44828 : List (Nat × Nat × Nat) := [(5879629824,110294760650490,110295146992186)]
theorem point_links_checked44828 : (cuts44828.take 1).map (fun c => (5879627777-1+2*2^10*c.k,110294756294056+c.lower,110295142635749+c.upper)) = pointBounds44828 := by
 decide +kernel
def cuts44829 : List PrefixCut := [⟨27,117046107,117046175⟩,
⟨64,278323800,278323960⟩]
theorem checked44829 : checkPrefixCuts (2^48) 5879758849 10 Manual.Count131072.C044829.packed 64 cuts44829 = true := by
 decide +kernel
def pointBounds44829 : List (Nat × Nat × Nat) := [(5879814144,110295155021214,110295541363137)]
theorem point_links_checked44829 : (cuts44829.take 1).map (fun c => (5879758849-1+2*2^10*c.k,110295037975107+c.lower,110295424316962+c.upper)) = pointBounds44829 := by
 decide +kernel
def cuts44830 : List PrefixCut := [⟨53,230591403,230591539⟩,
⟨64,278796292,278796456⟩]
theorem checked44830 : checkPrefixCuts (2^48) 5879889921 10 Manual.Count131072.C044830.packed 64 cuts44830 = true := by
 decide +kernel
def pointBounds44830 : List (Nat × Nat × Nat) := [(5879998464,110295546890310,110295933232461)]
theorem point_links_checked44830 : (cuts44830.take 1).map (fun c => (5879889921-1+2*2^10*c.k,110295316298907+c.lower,110295702640922+c.upper)) = pointBounds44830 := by
 decide +kernel
def cuts44831 : List PrefixCut := [⟨64,279220897,279221061⟩]
theorem checked44831 : checkPrefixCuts (2^48) 5880020993 10 Manual.Count131072.C044831.packed 64 cuts44831 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000150
