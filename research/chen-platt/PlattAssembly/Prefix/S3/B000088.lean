import PlattAssemblyKernel
import PlattCertificates.Count131072.C022816
import PlattCertificates.Count131072.C022817
import PlattCertificates.Count131072.C022818
import PlattCertificates.Count131072.C022819
import PlattCertificates.Count131072.C022820
import PlattCertificates.Count131072.C022821
import PlattCertificates.Count131072.C022822
import PlattCertificates.Count131072.C022823
import PlattCertificates.Count131072.C022824
import PlattCertificates.Count131072.C022825
import PlattCertificates.Count131072.C022826
import PlattCertificates.Count131072.C022827
import PlattCertificates.Count131072.C022828
import PlattCertificates.Count131072.C022829
import PlattCertificates.Count131072.C022830
import PlattCertificates.Count131072.C022831
import PlattCertificates.Count131072.C022832
import PlattCertificates.Count131072.C022833
import PlattCertificates.Count131072.C022834
import PlattCertificates.Count131072.C022835
import PlattCertificates.Count131072.C022836
import PlattCertificates.Count131072.C022837
import PlattCertificates.Count131072.C022838
import PlattCertificates.Count131072.C022839
import PlattCertificates.Count131072.C022840
import PlattCertificates.Count131072.C022841
import PlattCertificates.Count131072.C022842
import PlattCertificates.Count131072.C022843
import PlattCertificates.Count131072.C022844
import PlattCertificates.Count131072.C022845
import PlattCertificates.Count131072.C022846
import PlattCertificates.Count131072.C022847
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000088
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22816 : List PrefixCut := [⟨28,121915083,121915153⟩,
⟨120,526567107,526567411⟩,
⟨128,559183102,559183425⟩]
theorem checked22816 : checkPrefixCuts (2^48) 2994470913 9 Manual.Count131072.C022816.packed 128 cuts22816 = true := by
 decide +kernel
def pointBounds22816 : List (Nat × Nat × Nat) := [(2994499584,101722966286731,101723347639226),(2994593792,101723370938755,101723752291484)]
theorem point_links_checked22816 : (cuts22816.take 2).map (fun c => (2994470913-1+2*2^9*c.k,101722844371648+c.lower,101723225724073+c.upper)) = pointBounds22816 := by
 decide +kernel
def cuts22817 : List PrefixCut := [⟨84,365255800,365256011⟩,
⟨128,558782643,558782966⟩]
theorem checked22817 : checkPrefixCuts (2^48) 2994601985 9 Manual.Count131072.C022817.packed 128 cuts22817 = true := by
 decide +kernel
def pointBounds22817 : List (Nat × Nat × Nat) := [(2994688000,101723768810550,101724150163509)]
theorem point_links_checked22817 : (cuts22817.take 1).map (fun c => (2994601985-1+2*2^9*c.k,101723403554750+c.lower,101723784907498+c.upper)) = pointBounds22817 := by
 decide +kernel
def cuts22818 : List PrefixCut := [⟨48,210159877,210159997⟩,
⟨128,565149360,565149682⟩]
theorem checked22818 : checkPrefixCuts (2^48) 2994733057 9 Manual.Count131072.C022818.packed 128 cuts22818 = true := by
 decide +kernel
def pointBounds22818 : List (Nat × Nat × Nat) := [(2994782208,101724172497270,101724553850461)]
theorem point_links_checked22818 : (cuts22818.take 1).map (fun c => (2994733057-1+2*2^9*c.k,101723962337393+c.lower,101724343690464+c.upper)) = pointBounds22818 := by
 decide +kernel
def cuts22819 : List PrefixCut := [⟨12,51974078,51974109⟩,
⟨104,454507502,454507769⟩,
⟨128,560707319,560707643⟩]
theorem checked22819 : checkPrefixCuts (2^48) 2994864129 9 Manual.Count131072.C022819.packed 128 cuts22819 = true := by
 decide +kernel
def pointBounds22819 : List (Nat × Nat × Nat) := [(2994876416,101724579460831,101724960814255),(2994970624,101724981994255,101725363347915)]
theorem point_links_checked22819 : (cuts22819.take 2).map (fun c => (2994864129-1+2*2^9*c.k,101724527486753+c.lower,101724908840146+c.upper)) = pointBounds22819 := by
 decide +kernel
def cuts22820 : List PrefixCut := [⟨68,297730754,297730925⟩,
⟨128,563314279,563314602⟩]
theorem checked22820 : checkPrefixCuts (2^48) 2994995201 9 Manual.Count131072.C022820.packed 128 cuts22820 = true := by
 decide +kernel
def pointBounds22820 : List (Nat × Nat × Nat) := [(2995064832,101725385924826,101725767278714)]
theorem point_links_checked22820 : (cuts22820.take 1).map (fun c => (2994995201-1+2*2^9*c.k,101725088194072+c.lower,101725469547789+c.upper)) = pointBounds22820 := by
 decide +kernel
def cuts22821 : List PrefixCut := [⟨32,138992152,138992232⟩,
⟨124,546374385,546374698⟩,
⟨128,564887182,564887506⟩]
theorem checked22821 : checkPrefixCuts (2^48) 2995126273 9 Manual.Count131072.C022821.packed 128 cuts22821 = true := by
 decide +kernel
def pointBounds22821 : List (Nat × Nat × Nat) := [(2995159040,101725790500503,101726171854623),(2995253248,101726197882736,101726579237089)]
theorem point_links_checked22821 : (cuts22821.take 2).map (fun c => (2995126273-1+2*2^9*c.k,101725651508351+c.lower,101726032862391+c.upper)) = pointBounds22821 := by
 decide +kernel
def cuts22822 : List PrefixCut := [⟨88,384909828,384910048⟩,
⟨128,559882064,559882386⟩]
theorem checked22822 : checkPrefixCuts (2^48) 2995257345 9 Manual.Count131072.C022822.packed 128 cuts22822 = true := by
 decide +kernel
def pointBounds22822 : List (Nat × Nat × Nat) := [(2995347456,101726601305361,101726982659945)]
theorem point_links_checked22822 : (cuts22822.take 1).map (fun c => (2995257345-1+2*2^9*c.k,101726216395533+c.lower,101726597749897+c.upper)) = pointBounds22822 := by
 decide +kernel
def cuts22823 : List PrefixCut := [⟨52,234169737,234169871⟩,
⟨128,569912140,569912468⟩]
theorem checked22823 : checkPrefixCuts (2^48) 2995388417 9 Manual.Count131072.C022823.packed 128 cuts22823 = true := by
 decide +kernel
def pointBounds22823 : List (Nat × Nat × Nat) := [(2995441664,101727010447334,101727391802154)]
theorem point_links_checked22823 : (cuts22823.take 1).map (fun c => (2995388417-1+2*2^9*c.k,101726776277597+c.lower,101727157632283+c.upper)) = pointBounds22823 := by
 decide +kernel
def cuts22824 : List PrefixCut := [⟨16,70285849,70285892⟩,
⟨108,477334930,477335208⟩,
⟨128,565752713,565753039⟩]
theorem checked22824 : checkPrefixCuts (2^48) 2995519489 9 Manual.Count131072.C022824.packed 128 cuts22824 = true := by
 decide +kernel
def pointBounds22824 : List (Nat × Nat × Nat) := [(2995535872,101727416475586,101727797830643),(2995630080,101727823524667,101728204879959)]
theorem point_links_checked22824 : (cuts22824.take 2).map (fun c => (2995519489-1+2*2^9*c.k,101727346189737+c.lower,101727727544751+c.upper)) = pointBounds22824 := by
 decide +kernel
def cuts22825 : List PrefixCut := [⟨72,314672170,314672351⟩,
⟨128,566009731,566010051⟩]
theorem checked22825 : checkPrefixCuts (2^48) 2995650561 9 Manual.Count131072.C022825.packed 128 cuts22825 = true := by
 decide +kernel
def pointBounds22825 : List (Nat × Nat × Nat) := [(2995724288,101728226614620,101728607970141)]
theorem point_links_checked22825 : (cuts22825.take 1).map (fun c => (2995650561-1+2*2^9*c.k,101727911942450+c.lower,101728293297790+c.upper)) = pointBounds22825 := by
 decide +kernel
def cuts22826 : List PrefixCut := [⟨36,158222752,158222841⟩,
⟨128,567864128,567864449⟩]
theorem checked22826 : checkPrefixCuts (2^48) 2995781633 9 Manual.Count131072.C022826.packed 128 cuts22826 = true := by
 decide +kernel
def pointBounds22826 : List (Nat × Nat × Nat) := [(2995818496,101728636174933,101729017530682),(2995912704,101729045816309,101729427172290)]
theorem point_links_checked22826 : (cuts22826.take 2).map (fun c => (2995781633-1+2*2^9*c.k,101728477952181+c.lower,101728859307841+c.upper)) = pointBounds22826 := by
 decide +kernel
def cuts22827 : List PrefixCut := [⟨92,403239832,403240060⟩,
⟨128,564551014,564551331⟩]
theorem checked22827 : checkPrefixCuts (2^48) 2995912705 9 Manual.Count131072.C022827.packed 128 cuts22827 = true := by
 decide +kernel
def pointBounds22827 : List (Nat × Nat × Nat) := [(2996006912,101729449056141,101729830412350)]
theorem point_links_checked22827 : (cuts22827.take 1).map (fun c => (2995912705-1+2*2^9*c.k,101729045816309+c.lower,101729427172290+c.upper)) = pointBounds22827 := by
 decide +kernel
def cuts22828 : List PrefixCut := [⟨56,246519459,246519602⟩,
⟨128,567720440,567720769⟩]
theorem checked22828 : checkPrefixCuts (2^48) 2996043777 9 Manual.Count131072.C022828.packed 128 cuts22828 = true := by
 decide +kernel
def pointBounds22828 : List (Nat × Nat × Nat) := [(2996101120,101729856886782,101730238243223)]
theorem point_links_checked22828 : (cuts22828.take 1).map (fun c => (2996043777-1+2*2^9*c.k,101729610367323+c.lower,101729991723621+c.upper)) = pointBounds22828 := by
 decide +kernel
def cuts22829 : List PrefixCut := [⟨20,85959152,85959199⟩,
⟨112,489348745,489349021⟩,
⟨128,557549837,557550153⟩]
theorem checked22829 : checkPrefixCuts (2^48) 2996174849 9 Manual.Count131072.C022829.packed 128 cuts22829 = true := by
 decide +kernel
def pointBounds22829 : List (Nat × Nat × Nat) := [(2996195328,101730264046915,101730645403589),(2996289536,101730667436508,101731048793411)]
theorem point_links_checked22829 : (cuts22829.take 2).map (fun c => (2996174849-1+2*2^9*c.k,101730178087763+c.lower,101730559444390+c.upper)) = pointBounds22829 := by
 decide +kernel
def cuts22830 : List PrefixCut := [⟨76,331230410,331230601⟩,
⟨128,553862008,553862325⟩]
theorem checked22830 : checkPrefixCuts (2^48) 2996305921 9 Manual.Count131072.C022830.packed 128 cuts22830 = true := by
 decide +kernel
def pointBounds22830 : List (Nat × Nat × Nat) := [(2996383744,101731066868010,101731448225144)]
theorem point_links_checked22830 : (cuts22830.take 1).map (fun c => (2996305921-1+2*2^9*c.k,101730735637600+c.lower,101731116994543+c.upper)) = pointBounds22830 := by
 decide +kernel
def cuts22831 : List PrefixCut := [⟨40,175472245,175472348⟩,
⟨128,568773239,568773567⟩]
theorem checked22831 : checkPrefixCuts (2^48) 2996436993 9 Manual.Count131072.C022831.packed 128 cuts22831 = true := by
 decide +kernel
def pointBounds22831 : List (Nat × Nat × Nat) := [(2996477952,101731464971853,101731846329216)]
theorem point_links_checked22831 : (cuts22831.take 1).map (fun c => (2996436993-1+2*2^9*c.k,101731289499608+c.lower,101731670856868+c.upper)) = pointBounds22831 := by
 decide +kernel
def cuts22832 : List PrefixCut := [⟨4,18692540,18692550⟩,
⟨96,420622540,420622778⟩,
⟨128,561421862,561422176⟩]
theorem checked22832 : checkPrefixCuts (2^48) 2996568065 9 Manual.Count131072.C022832.packed 128 cuts22832 = true := by
 decide +kernel
def pointBounds22832 : List (Nat × Nat × Nat) := [(2996572160,101731876965387,101732258322985),(2996666368,101732278895387,101732660253213)]
theorem point_links_checked22832 : (cuts22832.take 2).map (fun c => (2996568065-1+2*2^9*c.k,101731858272847+c.lower,101732239630435+c.upper)) = pointBounds22832 := by
 decide +kernel
def cuts22833 : List PrefixCut := [⟨60,261211964,261212116⟩,
⟨128,557076686,557077007⟩]
theorem checked22833 : checkPrefixCuts (2^48) 2996699137 9 Manual.Count131072.C022833.packed 128 cuts22833 = true := by
 decide +kernel
def pointBounds22833 : List (Nat × Nat × Nat) := [(2996760576,101732680906673,101733062264727)]
theorem point_links_checked22833 : (cuts22833.take 1).map (fun c => (2996699137-1+2*2^9*c.k,101732419694709+c.lower,101732801052611+c.upper)) = pointBounds22833 := by
 decide +kernel
def cuts22834 : List PrefixCut := [⟨24,103691892,103691952⟩,
⟨116,509904381,509904677⟩,
⟨128,564096388,564096716⟩]
theorem checked22834 : checkPrefixCuts (2^48) 2996830209 9 Manual.Count131072.C022834.packed 128 cuts22834 = true := by
 decide +kernel
def pointBounds22834 : List (Nat × Nat × Nat) := [(2996854784,101733080463287,101733461821570),(2996948992,101733486675776,101733868034295)]
theorem point_links_checked22834 : (cuts22834.take 2).map (fun c => (2996830209-1+2*2^9*c.k,101732976771395+c.lower,101733358129618+c.upper)) = pointBounds22834 := by
 decide +kernel
def cuts22835 : List PrefixCut := [⟨80,353792186,353792390⟩,
⟨128,562663091,562663417⟩]
theorem checked22835 : checkPrefixCuts (2^48) 2996961281 9 Manual.Count131072.C022835.packed 128 cuts22835 = true := by
 decide +kernel
def pointBounds22835 : List (Nat × Nat × Nat) := [(2997043200,101733894659969,101734276018724)]
theorem point_links_checked22835 : (cuts22835.take 1).map (fun c => (2996961281-1+2*2^9*c.k,101733540867783+c.lower,101733922226334+c.upper)) = pointBounds22835 := by
 decide +kernel
def cuts22836 : List PrefixCut := [⟨44,199382119,199382234⟩,
⟨128,568085474,568085802⟩]
theorem checked22836 : checkPrefixCuts (2^48) 2997092353 9 Manual.Count131072.C022836.packed 128 cuts22836 = true := by
 decide +kernel
def pointBounds22836 : List (Nat × Nat × Nat) := [(2997137408,101734302912993,101734684271985)]
theorem point_links_checked22836 : (cuts22836.take 1).map (fun c => (2997092353-1+2*2^9*c.k,101734103530874+c.lower,101734484889751+c.upper)) = pointBounds22836 := by
 decide +kernel
def cuts22837 : List PrefixCut := [⟨8,37095141,37095162⟩,
⟨100,433583803,433584053⟩,
⟨128,557918300,557918619⟩]
theorem checked22837 : checkPrefixCuts (2^48) 2997223425 9 Manual.Count131072.C022837.packed 128 cuts22837 = true := by
 decide +kernel
def pointBounds22837 : List (Nat × Nat × Nat) := [(2997231616,101734708711489,101735090070715),(2997325824,101735105200151,101735486559606)]
theorem point_links_checked22837 : (cuts22837.take 2).map (fun c => (2997223425-1+2*2^9*c.k,101734671616348+c.lower,101735052975553+c.upper)) = pointBounds22837 := by
 decide +kernel
def cuts22838 : List PrefixCut := [⟨64,282565417,282565579⟩,
⟨128,562870916,562871240⟩]
theorem checked22838 : checkPrefixCuts (2^48) 2997354497 9 Manual.Count131072.C022838.packed 128 cuts22838 = true := by
 decide +kernel
def pointBounds22838 : List (Nat × Nat × Nat) := [(2997420032,101735512100065,101735893459751)]
theorem point_links_checked22838 : (cuts22838.take 1).map (fun c => (2997354497-1+2*2^9*c.k,101735229534648+c.lower,101735610894172+c.upper)) = pointBounds22838 := by
 decide +kernel
def cuts22839 : List PrefixCut := [⟨28,121041252,121041322⟩,
⟨120,527352119,527352423⟩,
⟨128,561813306,561813630⟩]
theorem checked22839 : checkPrefixCuts (2^48) 2997485569 9 Manual.Count131072.C022839.packed 128 cuts22839 = true := by
 decide +kernel
def pointBounds22839 : List (Nat × Nat × Nat) := [(2997514240,101735913446816,101736294806734),(2997608448,101736319757683,101736701117835)]
theorem point_links_checked22839 : (cuts22839.take 2).map (fun c => (2997485569-1+2*2^9*c.k,101735792405564+c.lower,101736173765412+c.upper)) = pointBounds22839 := by
 decide +kernel
def cuts22840 : List PrefixCut := [⟨84,367611515,367611724⟩,
⟨128,556624498,556624818⟩]
theorem checked22840 : checkPrefixCuts (2^48) 2997616641 9 Manual.Count131072.C022840.packed 128 cuts22840 = true := by
 decide +kernel
def pointBounds22840 : List (Nat × Nat × Nat) := [(2997702656,101736721830385,101737103190766)]
theorem point_links_checked22840 : (cuts22840.take 1).map (fun c => (2997616641-1+2*2^9*c.k,101736354218870+c.lower,101736735579042+c.upper)) = pointBounds22840 := by
 decide +kernel
def cuts22841 : List PrefixCut := [⟨48,208446239,208446355⟩,
⟨128,562233748,562234063⟩]
theorem checked22841 : checkPrefixCuts (2^48) 2997747713 9 Manual.Count131072.C022841.packed 128 cuts22841 = true := by
 decide +kernel
def pointBounds22841 : List (Nat × Nat × Nat) := [(2997796864,101737119289607,101737500650215)]
theorem point_links_checked22841 : (cuts22841.take 1).map (fun c => (2997747713-1+2*2^9*c.k,101736910843368+c.lower,101737292203860+c.upper)) = pointBounds22841 := by
 decide +kernel
def cuts22842 : List PrefixCut := [⟨12,53705745,53705779⟩,
⟨104,458181700,458181964⟩,
⟨128,568030240,568030563⟩]
theorem checked22842 : checkPrefixCuts (2^48) 2997878785 9 Manual.Count131072.C022842.packed 128 cuts22842 = true := by
 decide +kernel
def pointBounds22842 : List (Nat × Nat × Nat) := [(2997891072,101737526782861,101737908143702),(2997985280,101737931258816,101738312619887)]
theorem point_links_checked22842 : (cuts22842.take 2).map (fun c => (2997878785-1+2*2^9*c.k,101737473077116+c.lower,101737854437923+c.upper)) = pointBounds22842 := by
 decide +kernel
def cuts22843 : List PrefixCut := [⟨68,298745749,298745922⟩,
⟨128,563217278,563217601⟩]
theorem checked22843 : checkPrefixCuts (2^48) 2998009857 9 Manual.Count131072.C022843.packed 128 cuts22843 = true := by
 decide +kernel
def pointBounds22843 : List (Nat × Nat × Nat) := [(2998079488,101738339853105,101738721214408)]
theorem point_links_checked22843 : (cuts22843.take 1).map (fun c => (2998009857-1+2*2^9*c.k,101738041107356+c.lower,101738422468486+c.upper)) = pointBounds22843 := by
 decide +kernel
def cuts22844 : List PrefixCut := [⟨32,139697374,139697449⟩,
⟨124,543947411,543947724⟩,
⟨128,560282375,560282697⟩]
theorem checked22844 : checkPrefixCuts (2^48) 2998140929 9 Manual.Count131072.C022844.packed 128 cuts22844 = true := by
 decide +kernel
def pointBounds22844 : List (Nat × Nat × Nat) := [(2998173696,101738744022008,101739125383536),(2998267904,101739148272045,101739529633811)]
theorem point_links_checked22844 : (cuts22844.take 2).map (fun c => (2998140929-1+2*2^9*c.k,101738604324634+c.lower,101738985686087+c.upper)) = pointBounds22844 := by
 decide +kernel
def cuts22845 : List PrefixCut := [⟨88,385367712,385367934⟩,
⟨128,558662026,558662347⟩]
theorem checked22845 : checkPrefixCuts (2^48) 2998272001 9 Manual.Count131072.C022845.packed 128 cuts22845 = true := by
 decide +kernel
def pointBounds22845 : List (Nat × Nat × Nat) := [(2998362112,101739549974721,101739931336718)]
theorem point_links_checked22845 : (cuts22845.take 1).map (fun c => (2998272001-1+2*2^9*c.k,101739164607009+c.lower,101739545968784+c.upper)) = pointBounds22845 := by
 decide +kernel
def cuts22846 : List PrefixCut := [⟨52,231399683,231399819⟩,
⟨128,560233455,560233778⟩]
theorem checked22846 : checkPrefixCuts (2^48) 2998403073 9 Manual.Count131072.C022846.packed 128 cuts22846 = true := by
 decide +kernel
def pointBounds22846 : List (Nat × Nat × Nat) := [(2998456320,101739954668718,101740336030950)]
theorem point_links_checked22846 : (cuts22846.take 1).map (fun c => (2998403073-1+2*2^9*c.k,101739723269035+c.lower,101740104631131+c.upper)) = pointBounds22846 := by
 decide +kernel
def cuts22847 : List PrefixCut := [⟨16,69276487,69276529⟩,
⟨108,478920196,478920472⟩,
⟨128,567812291,567812616⟩]
theorem checked22847 : checkPrefixCuts (2^48) 2998534145 9 Manual.Count131072.C022847.packed 128 cuts22847 = true := by
 decide +kernel
def pointBounds22847 : List (Nat × Nat × Nat) := [(2998550528,101740352778977,101740734141438),(2998644736,101740762422686,101741143785381)]
theorem point_links_checked22847 : (cuts22847.take 2).map (fun c => (2998534145-1+2*2^9*c.k,101740283502490+c.lower,101740664864909+c.upper)) = pointBounds22847 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000088
