import PlattAssemblyKernel
import PlattCertificates.Count131072.C054736
import PlattCertificates.Count131072.C054737
import PlattCertificates.Count131072.C054738
import PlattCertificates.Count131072.C054739
import PlattCertificates.Count131072.C054740
import PlattCertificates.Count131072.C054741
import PlattCertificates.Count131072.C054742
import PlattCertificates.Count131072.C054743
import PlattCertificates.Count131072.C054744
import PlattCertificates.Count131072.C054745
import PlattCertificates.Count131072.C054746
import PlattCertificates.Count131072.C054747
import PlattCertificates.Count131072.C054748
import PlattCertificates.Count131072.C054749
import PlattCertificates.Count131072.C054750
import PlattCertificates.Count131072.C054751
import PlattCertificates.Count131072.C054752
import PlattCertificates.Count131072.C054753
import PlattCertificates.Count131072.C054754
import PlattCertificates.Count131072.C054755
import PlattCertificates.Count131072.C054756
import PlattCertificates.Count131072.C054757
import PlattCertificates.Count131072.C054758
import PlattCertificates.Count131072.C054759
import PlattCertificates.Count131072.C054760
import PlattCertificates.Count131072.C054761
import PlattCertificates.Count131072.C054762
import PlattCertificates.Count131072.C054763
import PlattCertificates.Count131072.C054764
import PlattCertificates.Count131072.C054765
import PlattCertificates.Count131072.C054766
import PlattCertificates.Count131072.C054767
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000148
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts54736 : List PrefixCut := [⟨64,223623835,223623963⟩]
theorem checked54736 : checkPrefixCuts (2^48) 7178289153 10 Manual.Count131072.C054736.packed 64 cuts54736 = true := by
 decide +kernel
def cuts54737 : List PrefixCut := [⟨25,88421075,88421126⟩,
⟨64,225423481,225423609⟩]
theorem checked54737 : checkPrefixCuts (2^48) 7178420225 10 Manual.Count131072.C054737.packed 64 cuts54737 = true := by
 decide +kernel
def pointBounds54737 : List (Nat × Nat × Nat) := [(7178471424,112781198468669,112781586229617)]
theorem point_links_checked54737 : (cuts54737.take 1).map (fun c => (7178420225-1+2*2^10*c.k,112781110047594+c.lower,112781497808491+c.upper)) = pointBounds54737 := by
 decide +kernel
def cuts54738 : List PrefixCut := [⟨64,228713006,228713134⟩]
theorem checked54738 : checkPrefixCuts (2^48) 7178551297 10 Manual.Count131072.C054738.packed 64 cuts54738 = true := by
 decide +kernel
def cuts54739 : List PrefixCut := [⟨7,23408244,23408257⟩,
⟨64,220788512,220788637⟩]
theorem checked54739 : checkPrefixCuts (2^48) 7178682369 10 Manual.Count131072.C054739.packed 64 cuts54739 = true := by
 decide +kernel
def pointBounds54739 : List (Nat × Nat × Nat) := [(7178696704,112781587592325,112781975353491)]
theorem point_links_checked54739 : (cuts54739.take 1).map (fun c => (7178682369-1+2*2^10*c.k,112781564184081+c.lower,112781951945234+c.upper)) = pointBounds54739 := by
 decide +kernel
def cuts54740 : List PrefixCut := [⟨53,188712011,188712119⟩,
⟨64,227371551,227371681⟩]
theorem checked54740 : checkPrefixCuts (2^48) 7178813441 10 Manual.Count131072.C054740.packed 64 cuts54740 = true := by
 decide +kernel
def pointBounds54740 : List (Nat × Nat × Nat) := [(7178921984,112781973684604,112782361445990)]
theorem point_links_checked54740 : (cuts54740.take 1).map (fun c => (7178813441-1+2*2^10*c.k,112781784972593+c.lower,112782172733871+c.upper)) = pointBounds54740 := by
 decide +kernel
def cuts54741 : List PrefixCut := [⟨64,226661658,226661789⟩]
theorem checked54741 : checkPrefixCuts (2^48) 7178944513 10 Manual.Count131072.C054741.packed 64 cuts54741 = true := by
 decide +kernel
def cuts54742 : List PrefixCut := [⟨35,124522972,124523043⟩,
⟨64,227912159,227912289⟩]
theorem checked54742 : checkPrefixCuts (2^48) 7179075585 10 Manual.Count131072.C054742.packed 64 cuts54742 = true := by
 decide +kernel
def pointBounds54742 : List (Nat × Nat × Nat) := [(7179147264,112782363528774,112782751290384)]
theorem point_links_checked54742 : (cuts54742.take 1).map (fun c => (7179075585-1+2*2^10*c.k,112782239005802+c.lower,112782626767341+c.upper)) = pointBounds54742 := by
 decide +kernel
def cuts54743 : List PrefixCut := [⟨64,227711978,227712104⟩]
theorem checked54743 : checkPrefixCuts (2^48) 7179206657 10 Manual.Count131072.C054743.packed 64 cuts54743 = true := by
 decide +kernel
def cuts54744 : List PrefixCut := [⟨17,61200805,61200839⟩,
⟨64,226453242,226453369⟩]
theorem checked54744 : checkPrefixCuts (2^48) 7179337729 10 Manual.Count131072.C054744.packed 64 cuts54744 = true := by
 decide +kernel
def pointBounds54744 : List (Nat × Nat × Nat) := [(7179372544,112782755830744,112783143592573)]
theorem point_links_checked54744 : (cuts54744.take 1).map (fun c => (7179337729-1+2*2^10*c.k,112782694629939+c.lower,112783082391734+c.upper)) = pointBounds54744 := by
 decide +kernel
def cuts54745 : List PrefixCut := [⟨63,224998524,224998649⟩,
⟨64,228801392,228801519⟩]
theorem checked54745 : checkPrefixCuts (2^48) 7179468801 10 Manual.Count131072.C054745.packed 64 cuts54745 = true := by
 decide +kernel
def pointBounds54745 : List (Nat × Nat × Nat) := [(7179597824,112783146081705,112783533843752)]
theorem point_links_checked54745 : (cuts54745.take 1).map (fun c => (7179468801-1+2*2^10*c.k,112782921083181+c.lower,112783308845103+c.upper)) = pointBounds54745 := by
 decide +kernel
def cuts54746 : List PrefixCut := [⟨64,226876222,226876350⟩]
theorem checked54746 : checkPrefixCuts (2^48) 7179599873 10 Manual.Count131072.C054746.packed 64 cuts54746 = true := by
 decide +kernel
def cuts54747 : List PrefixCut := [⟨45,158265940,158266031⟩,
⟨64,225186300,225186429⟩]
theorem checked54747 : checkPrefixCuts (2^48) 7179730945 10 Manual.Count131072.C054747.packed 64 cuts54747 = true := by
 decide +kernel
def pointBounds54747 : List (Nat × Nat × Nat) := [(7179823104,112783535026735,112783922789003)]
theorem point_links_checked54747 : (cuts54747.take 1).map (fun c => (7179730945-1+2*2^10*c.k,112783376760795+c.lower,112783764522972+c.upper)) = pointBounds54747 := by
 decide +kernel
def cuts54748 : List PrefixCut := [⟨64,222241969,222242096⟩]
theorem checked54748 : checkPrefixCuts (2^48) 7179862017 10 Manual.Count131072.C054748.packed 64 cuts54748 = true := by
 decide +kernel
def cuts54749 : List PrefixCut := [⟨27,96398991,96399047⟩,
⟨64,227138202,227138332⟩]
theorem checked54749 : checkPrefixCuts (2^48) 7179993089 10 Manual.Count131072.C054749.packed 64 cuts54749 = true := by
 decide +kernel
def pointBounds54749 : List (Nat × Nat × Nat) := [(7180048384,112783920588055,112784308350544)]
theorem point_links_checked54749 : (cuts54749.take 1).map (fun c => (7179993089-1+2*2^10*c.k,112783824189064+c.lower,112784211951497+c.upper)) = pointBounds54749 := by
 decide +kernel
def cuts54750 : List PrefixCut := [⟨64,225644370,225644497⟩]
theorem checked54750 : checkPrefixCuts (2^48) 7180124161 10 Manual.Count131072.C054750.packed 64 cuts54750 = true := by
 decide +kernel
def cuts54751 : List PrefixCut := [⟨9,31948969,31948988⟩,
⟨64,227012292,227012420⟩]
theorem checked54751 : checkPrefixCuts (2^48) 7180255233 10 Manual.Count131072.C054751.packed 64 cuts54751 = true := by
 decide +kernel
def pointBounds54751 : List (Nat × Nat × Nat) := [(7180273664,112784308920605,112784696683314)]
theorem point_links_checked54751 : (cuts54751.take 1).map (fun c => (7180255233-1+2*2^10*c.k,112784276971636+c.lower,112784664734326+c.upper)) = pointBounds54751 := by
 decide +kernel
def cuts54752 : List PrefixCut := [⟨55,191924248,191924357⟩,
⟨64,223166533,223166660⟩]
theorem checked54752 : checkPrefixCuts (2^48) 7180386305 10 Manual.Count131072.C054752.packed 64 cuts54752 = true := by
 decide +kernel
def pointBounds54752 : List (Nat × Nat × Nat) := [(7180498944,112784695908176,112785083671103)]
theorem point_links_checked54752 : (cuts54752.take 1).map (fun c => (7180386305-1+2*2^10*c.k,112784503983928+c.lower,112784891746746+c.upper)) = pointBounds54752 := by
 decide +kernel
def cuts54753 : List PrefixCut := [⟨64,223828866,223828995⟩]
theorem checked54753 : checkPrefixCuts (2^48) 7180517377 10 Manual.Count131072.C054753.packed 64 cuts54753 = true := by
 decide +kernel
def cuts54754 : List PrefixCut := [⟨37,132492225,132492298⟩,
⟨64,227705444,227705570⟩]
theorem checked54754 : checkPrefixCuts (2^48) 7180648449 10 Manual.Count131072.C054754.packed 64 cuts54754 = true := by
 decide +kernel
def pointBounds54754 : List (Nat × Nat × Nat) := [(7180724224,112785083471552,112785471234699)]
theorem point_links_checked54754 : (cuts54754.take 1).map (fun c => (7180648449-1+2*2^10*c.k,112784950979327+c.lower,112785338742401+c.upper)) = pointBounds54754 := by
 decide +kernel
def cuts54755 : List PrefixCut := [⟨64,225192619,225192744⟩]
theorem checked54755 : checkPrefixCuts (2^48) 7180779521 10 Manual.Count131072.C054755.packed 64 cuts54755 = true := by
 decide +kernel
def cuts54756 : List PrefixCut := [⟨19,66792636,66792676⟩,
⟨64,225266907,225267035⟩]
theorem checked54756 : checkPrefixCuts (2^48) 7180910593 10 Manual.Count131072.C054756.packed 64 cuts54756 = true := by
 decide +kernel
def pointBounds54756 : List (Nat × Nat × Nat) := [(7180949504,112785470670026,112785858433391)]
theorem point_links_checked54756 : (cuts54756.take 1).map (fun c => (7180910593-1+2*2^10*c.k,112785403877390+c.lower,112785791640715+c.upper)) = pointBounds54756 := by
 decide +kernel
def cuts54757 : List PrefixCut := [⟨64,227340213,227340343⟩]
theorem checked54757 : checkPrefixCuts (2^48) 7181041665 10 Manual.Count131072.C054757.packed 64 cuts54757 = true := by
 decide +kernel
def cuts54758 : List PrefixCut := [⟨1,3841230,3841232⟩,
⟨64,228119958,228120086⟩]
theorem checked54758 : checkPrefixCuts (2^48) 7181172737 10 Manual.Count131072.C054758.packed 64 cuts54758 = true := by
 decide +kernel
def pointBounds54758 : List (Nat × Nat × Nat) := [(7181174784,112785860325740,112786248089325)]
theorem point_links_checked54758 : (cuts54758.take 1).map (fun c => (7181172737-1+2*2^10*c.k,112785856484510+c.lower,112786244248093+c.upper)) = pointBounds54758 := by
 decide +kernel
def cuts54759 : List PrefixCut := [⟨47,167128532,167128627⟩,
⟨64,225920873,225921002⟩]
theorem checked54759 : checkPrefixCuts (2^48) 7181303809 10 Manual.Count131072.C054759.packed 64 cuts54759 = true := by
 decide +kernel
def pointBounds54759 : List (Nat × Nat × Nat) := [(7181400064,112786251733000,112786639496806)]
theorem point_links_checked54759 : (cuts54759.take 1).map (fun c => (7181303809-1+2*2^10*c.k,112786084604468+c.lower,112786472368179+c.upper)) = pointBounds54759 := by
 decide +kernel
def cuts54760 : List PrefixCut := [⟨64,227092578,227092705⟩]
theorem checked54760 : checkPrefixCuts (2^48) 7181434881 10 Manual.Count131072.C054760.packed 64 cuts54760 = true := by
 decide +kernel
def cuts54761 : List PrefixCut := [⟨29,102413711,102413770⟩,
⟨64,226814082,226814211⟩]
theorem checked54761 : checkPrefixCuts (2^48) 7181565953 10 Manual.Count131072.C054761.packed 64 cuts54761 = true := by
 decide +kernel
def pointBounds54761 : List (Nat × Nat × Nat) := [(7181625344,112786640031630,112787027795656)]
theorem point_links_checked54761 : (cuts54761.take 1).map (fun c => (7181565953-1+2*2^10*c.k,112786537617919+c.lower,112786925381886+c.upper)) = pointBounds54761 := by
 decide +kernel
def cuts54762 : List PrefixCut := [⟨64,224066423,224066552⟩]
theorem checked54762 : checkPrefixCuts (2^48) 7181697025 10 Manual.Count131072.C054762.packed 64 cuts54762 = true := by
 decide +kernel
def cuts54763 : List PrefixCut := [⟨11,39623711,39623734⟩,
⟨64,225434087,225434217⟩]
theorem checked54763 : checkPrefixCuts (2^48) 7181828097 10 Manual.Count131072.C054763.packed 64 cuts54763 = true := by
 decide +kernel
def pointBounds54763 : List (Nat × Nat × Nat) := [(7181850624,112787028122135,112787415886383)]
theorem point_links_checked54763 : (cuts54763.take 1).map (fun c => (7181828097-1+2*2^10*c.k,112786988498424+c.lower,112787376262649+c.upper)) = pointBounds54763 := by
 decide +kernel
def cuts54764 : List PrefixCut := [⟨57,200425937,200426049⟩,
⟨64,224450181,224450307⟩]
theorem checked54764 : checkPrefixCuts (2^48) 7181959169 10 Manual.Count131072.C054764.packed 64 cuts54764 = true := by
 decide +kernel
def pointBounds54764 : List (Nat × Nat × Nat) := [(7182075904,112787414358448,112787802122915)]
theorem point_links_checked54764 : (cuts54764.take 1).map (fun c => (7181959169-1+2*2^10*c.k,112787213932511+c.lower,112787601696866+c.upper)) = pointBounds54764 := by
 decide +kernel
def cuts54765 : List PrefixCut := [⟨64,226444820,226444949⟩]
theorem checked54765 : checkPrefixCuts (2^48) 7182090241 10 Manual.Count131072.C054765.packed 64 cuts54765 = true := by
 decide +kernel
def cuts54766 : List PrefixCut := [⟨39,137479534,137479610⟩,
⟨64,225656887,225657013⟩]
theorem checked54766 : checkPrefixCuts (2^48) 7182221313 10 Manual.Count131072.C054766.packed 64 cuts54766 = true := by
 decide +kernel
def pointBounds54766 : List (Nat × Nat × Nat) := [(7182301184,112787802307046,112788190071732)]
theorem point_links_checked54766 : (cuts54766.take 1).map (fun c => (7182221313-1+2*2^10*c.k,112787664827512+c.lower,112788052592122+c.upper)) = pointBounds54766 := by
 decide +kernel
def cuts54767 : List PrefixCut := [⟨64,227455473,227455600⟩]
theorem checked54767 : checkPrefixCuts (2^48) 7182352385 10 Manual.Count131072.C054767.packed 64 cuts54767 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000148
