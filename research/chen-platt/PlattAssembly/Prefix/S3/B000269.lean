import PlattAssemblyKernel
import PlattCertificates.Count131072.C028608
import PlattCertificates.Count131072.C028609
import PlattCertificates.Count131072.C028610
import PlattCertificates.Count131072.C028611
import PlattCertificates.Count131072.C028612
import PlattCertificates.Count131072.C028613
import PlattCertificates.Count131072.C028614
import PlattCertificates.Count131072.C028615
import PlattCertificates.Count131072.C028616
import PlattCertificates.Count131072.C028617
import PlattCertificates.Count131072.C028618
import PlattCertificates.Count131072.C028619
import PlattCertificates.Count131072.C028620
import PlattCertificates.Count131072.C028621
import PlattCertificates.Count131072.C028622
import PlattCertificates.Count131072.C028623
import PlattCertificates.Count131072.C028624
import PlattCertificates.Count131072.C028625
import PlattCertificates.Count131072.C028626
import PlattCertificates.Count131072.C028627
import PlattCertificates.Count131072.C028628
import PlattCertificates.Count131072.C028629
import PlattCertificates.Count131072.C028630
import PlattCertificates.Count131072.C028631
import PlattCertificates.Count131072.C028632
import PlattCertificates.Count131072.C028633
import PlattCertificates.Count131072.C028634
import PlattCertificates.Count131072.C028635
import PlattCertificates.Count131072.C028636
import PlattCertificates.Count131072.C028637
import PlattCertificates.Count131072.C028638
import PlattCertificates.Count131072.C028639
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000269
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28608 : List PrefixCut := [⟨68,238007143,238007276⟩,
⟨128,443616522,443616772⟩]
theorem checked28608 : checkPrefixCuts (2^48) 3753639937 9 Manual.Count131072.C028608.packed 128 cuts28608 = true := by
 decide +kernel
def pointBounds28608 : List (Nat × Nat × Nat) := [(3753709568,104622958413480,104623341395560)]
theorem point_links_checked28608 : (cuts28608.take 1).map (fun c => (3753639937-1+2*2^9*c.k,104622720406337+c.lower,104623103388284+c.upper)) = pointBounds28608 := by
 decide +kernel
def cuts28609 : List PrefixCut := [⟨55,192558930,192559039⟩,
⟨128,443226096,443226343⟩]
theorem checked28609 : checkPrefixCuts (2^48) 3753771009 9 Manual.Count131072.C028609.packed 128 cuts28609 = true := by
 decide +kernel
def pointBounds28609 : List (Nat × Nat × Nat) := [(3753827328,104623356581789,104623739564095)]
theorem point_links_checked28609 : (cuts28609.take 1).map (fun c => (3753771009-1+2*2^9*c.k,104623164022859+c.lower,104623547005056+c.upper)) = pointBounds28609 := by
 decide +kernel
def cuts28610 : List PrefixCut := [⟨42,144564377,144564459⟩,
⟨128,440661242,440661488⟩]
theorem checked28610 : checkPrefixCuts (2^48) 3753902081 9 Manual.Count131072.C028610.packed 128 cuts28610 = true := by
 decide +kernel
def pointBounds28610 : List (Nat × Nat × Nat) := [(3753945088,104623751813332,104624134795858)]
theorem point_links_checked28610 : (cuts28610.take 1).map (fun c => (3753902081-1+2*2^9*c.k,104623607248955+c.lower,104623990231399+c.upper)) = pointBounds28610 := by
 decide +kernel
def cuts28611 : List PrefixCut := [⟨29,99422205,99422262⟩,
⟨128,443944869,443945120⟩]
theorem checked28611 : checkPrefixCuts (2^48) 3754033153 9 Manual.Count131072.C028611.packed 128 cuts28611 = true := by
 decide +kernel
def pointBounds28611 : List (Nat × Nat × Nat) := [(3754062848,104624147332402,104624530315149)]
theorem point_links_checked28611 : (cuts28611.take 1).map (fun c => (3754033153-1+2*2^9*c.k,104624047910197+c.lower,104624430892887+c.upper)) = pointBounds28611 := by
 decide +kernel
def cuts28612 : List PrefixCut := [⟨16,54582931,54582959⟩,
⟨128,448203021,448203267⟩]
theorem checked28612 : checkPrefixCuts (2^48) 3754164225 9 Manual.Count131072.C028612.packed 128 cuts28612 = true := by
 decide +kernel
def pointBounds28612 : List (Nat × Nat × Nat) := [(3754180608,104624546437997,104624929420966)]
theorem point_links_checked28612 : (cuts28612.take 1).map (fun c => (3754164225-1+2*2^9*c.k,104624491855066+c.lower,104624874838007+c.upper)) = pointBounds28612 := by
 decide +kernel
def cuts28613 : List PrefixCut := [⟨3,10721291,10721298⟩,
⟨118,409951750,409951984⟩,
⟨128,446237995,446238249⟩]
theorem checked28613 : checkPrefixCuts (2^48) 3754295297 9 Manual.Count131072.C028613.packed 128 cuts28613 = true := by
 decide +kernel
def pointBounds28613 : List (Nat × Nat × Nat) := [(3754298368,104624950779378,104625333762572),(3754416128,104625350009837,104625732993258)]
theorem point_links_checked28613 : (cuts28613.take 2).map (fun c => (3754295297-1+2*2^9*c.k,104624940058087+c.lower,104625323041274+c.upper)) = pointBounds28613 := by
 decide +kernel
def cuts28614 : List PrefixCut := [⟨105,367205058,367205260⟩,
⟨128,447796835,447797082⟩]
theorem checked28614 : checkPrefixCuts (2^48) 3754426369 9 Manual.Count131072.C028614.packed 128 cuts28614 = true := by
 decide +kernel
def pointBounds28614 : List (Nat × Nat × Nat) := [(3754533888,104625753501140,104626136484783)]
theorem point_links_checked28614 : (cuts28614.take 1).map (fun c => (3754426369-1+2*2^9*c.k,104625386296082+c.lower,104625769279523+c.upper)) = pointBounds28614 := by
 decide +kernel
def cuts28615 : List PrefixCut := [⟨92,316364636,316364813⟩,
⟨128,439684710,439684958⟩]
theorem checked28615 : checkPrefixCuts (2^48) 3754557441 9 Manual.Count131072.C028615.packed 128 cuts28615 = true := by
 decide +kernel
def pointBounds28615 : List (Nat × Nat × Nat) := [(3754651648,104626150457553,104626533441418)]
theorem point_links_checked28615 : (cuts28615.take 1).map (fun c => (3754557441-1+2*2^9*c.k,104625834092917+c.lower,104626217076605+c.upper)) = pointBounds28615 := by
 decide +kernel
def cuts28616 : List PrefixCut := [⟨79,276097722,276097878⟩,
⟨128,448515217,448515470⟩]
theorem checked28616 : checkPrefixCuts (2^48) 3754688513 9 Manual.Count131072.C028616.packed 128 cuts28616 = true := by
 decide +kernel
def pointBounds28616 : List (Nat × Nat × Nat) := [(3754769408,104626549875349,104626932859441)]
theorem point_links_checked28616 : (cuts28616.take 1).map (fun c => (3754688513-1+2*2^9*c.k,104626273777627+c.lower,104626656761563+c.upper)) = pointBounds28616 := by
 decide +kernel
def cuts28617 : List PrefixCut := [⟨66,227362655,227362782⟩,
⟨128,442952330,442952580⟩]
theorem checked28617 : checkPrefixCuts (2^48) 3754819585 9 Manual.Count131072.C028617.packed 128 cuts28617 = true := by
 decide +kernel
def pointBounds28617 : List (Nat × Nat × Nat) := [(3754887168,104626949655499,104627332639815)]
theorem point_links_checked28617 : (cuts28617.take 1).map (fun c => (3754819585-1+2*2^9*c.k,104626722292844+c.lower,104627105277033+c.upper)) = pointBounds28617 := by
 decide +kernel
def cuts28618 : List PrefixCut := [⟨53,184327784,184327892⟩,
⟨128,447134624,447134878⟩]
theorem checked28618 : checkPrefixCuts (2^48) 3754950657 9 Manual.Count131072.C028618.packed 128 cuts28618 = true := by
 decide +kernel
def pointBounds28618 : List (Nat × Nat × Nat) := [(3755004928,104627349572958,104627732557505)]
theorem point_links_checked28618 : (cuts28618.take 1).map (fun c => (3754950657-1+2*2^9*c.k,104627165245174+c.lower,104627548229613+c.upper)) = pointBounds28618 := by
 decide +kernel
def cuts28619 : List PrefixCut := [⟨40,138822189,138822268⟩,
⟨128,440297913,440298163⟩]
theorem checked28619 : checkPrefixCuts (2^48) 3755081729 9 Manual.Count131072.C028619.packed 128 cuts28619 = true := by
 decide +kernel
def pointBounds28619 : List (Nat × Nat × Nat) := [(3755122688,104627751201987,104628134186759)]
theorem point_links_checked28619 : (cuts28619.take 1).map (fun c => (3755081729-1+2*2^9*c.k,104627612379798+c.lower,104627995364491+c.upper)) = pointBounds28619 := by
 decide +kernel
def cuts28620 : List PrefixCut := [⟨27,94069156,94069207⟩,
⟨128,445904141,445904392⟩]
theorem checked28620 : checkPrefixCuts (2^48) 3755212801 9 Manual.Count131072.C028620.packed 128 cuts28620 = true := by
 decide +kernel
def pointBounds28620 : List (Nat × Nat × Nat) := [(3755240448,104628146746867,104628529731861)]
theorem point_links_checked28620 : (cuts28620.take 1).map (fun c => (3755212801-1+2*2^9*c.k,104628052677711+c.lower,104628435662654+c.upper)) = pointBounds28620 := by
 decide +kernel
def cuts28621 : List PrefixCut := [⟨14,50218520,50218546⟩,
⟨128,447462521,447462770⟩]
theorem checked28621 : checkPrefixCuts (2^48) 3755343873 9 Manual.Count131072.C028621.packed 128 cuts28621 = true := by
 decide +kernel
def pointBounds28621 : List (Nat × Nat × Nat) := [(3755358208,104628548800372,104628931785592)]
theorem point_links_checked28621 : (cuts28621.take 1).map (fun c => (3755343873-1+2*2^9*c.k,104628498581852+c.lower,104628881567046+c.upper)) = pointBounds28621 := by
 decide +kernel
def cuts28622 : List PrefixCut := [⟨1,3222873,3222875⟩,
⟨116,401428779,401428999⟩,
⟨128,442875049,442875293⟩]
theorem checked28622 : checkPrefixCuts (2^48) 3755474945 9 Manual.Count131072.C028622.packed 128 cuts28622 = true := by
 decide +kernel
def pointBounds28622 : List (Nat × Nat × Nat) := [(3755475968,104628949267246,104629332252691),(3755593728,104629347473152,104629730458815)]
theorem point_links_checked28622 : (cuts28622.take 2).map (fun c => (3755474945-1+2*2^9*c.k,104628946044373+c.lower,104629329029816+c.upper)) = pointBounds28622 := by
 decide +kernel
def cuts28623 : List PrefixCut := [⟨103,359220400,359220598⟩,
⟨128,446831769,446832015⟩]
theorem checked28623 : checkPrefixCuts (2^48) 3755606017 9 Manual.Count131072.C028623.packed 128 cuts28623 = true := by
 decide +kernel
def pointBounds28623 : List (Nat × Nat × Nat) := [(3755711488,104629748139822,104630131125707)]
theorem point_links_checked28623 : (cuts28623.take 1).map (fun c => (3755606017-1+2*2^9*c.k,104629388919422+c.lower,104629771905109+c.upper)) = pointBounds28623 := by
 decide +kernel
def cuts28624 : List PrefixCut := [⟨90,310794358,310794537⟩,
⟨128,445467073,445467327⟩]
theorem checked28624 : checkPrefixCuts (2^48) 3755737089 9 Manual.Count131072.C028624.packed 128 cuts28624 = true := by
 decide +kernel
def pointBounds28624 : List (Nat × Nat × Nat) := [(3755829248,104630146545549,104630529531661)]
theorem point_links_checked28624 : (cuts28624.take 1).map (fun c => (3755737089-1+2*2^9*c.k,104629835751191+c.lower,104630218737124+c.upper)) = pointBounds28624 := by
 decide +kernel
def cuts28625 : List PrefixCut := [⟨77,267092938,267093087⟩,
⟨128,443278284,443278531⟩]
theorem checked28625 : checkPrefixCuts (2^48) 3755868161 9 Manual.Count131072.C028625.packed 128 cuts28625 = true := by
 decide +kernel
def pointBounds28625 : List (Nat × Nat × Nat) := [(3755947008,104630548311202,104630931297538)]
theorem point_links_checked28625 : (cuts28625.take 1).map (fun c => (3755868161-1+2*2^9*c.k,104630281218264+c.lower,104630664204451+c.upper)) = pointBounds28625 := by
 decide +kernel
def cuts28626 : List PrefixCut := [⟨64,224668433,224668562⟩,
⟨128,442513563,442513810⟩]
theorem checked28626 : checkPrefixCuts (2^48) 3755999233 9 Manual.Count131072.C028626.packed 128 cuts28626 = true := by
 decide +kernel
def pointBounds28626 : List (Nat × Nat × Nat) := [(3756064768,104630949164981,104631332151544)]
theorem point_links_checked28626 : (cuts28626.take 1).map (fun c => (3755999233-1+2*2^9*c.k,104630724496548+c.lower,104631107482982+c.upper)) = pointBounds28626 := by
 decide +kernel
def cuts28627 : List PrefixCut := [⟨51,177450674,177450774⟩,
⟨128,444746122,444746369⟩]
theorem checked28627 : checkPrefixCuts (2^48) 3756130305 9 Manual.Count131072.C028627.packed 128 cuts28627 = true := by
 decide +kernel
def pointBounds28627 : List (Nat × Nat × Nat) := [(3756182528,104631344460785,104631727447566)]
theorem point_links_checked28627 : (cuts28627.take 1).map (fun c => (3756130305-1+2*2^9*c.k,104631167010111+c.lower,104631549996792+c.upper)) = pointBounds28627 := by
 decide +kernel
def cuts28628 : List PrefixCut := [⟨38,133683079,133683151⟩,
⟨128,449226630,449226873⟩]
theorem checked28628 : checkPrefixCuts (2^48) 3756261377 9 Manual.Count131072.C028628.packed 128 cuts28628 = true := by
 decide +kernel
def pointBounds28628 : List (Nat × Nat × Nat) := [(3756300288,104631745439312,104632128426312)]
theorem point_links_checked28628 : (cuts28628.take 1).map (fun c => (3756261377-1+2*2^9*c.k,104631611756233+c.lower,104631994743161+c.upper)) = pointBounds28628 := by
 decide +kernel
def cuts28629 : List PrefixCut := [⟨25,86771238,86771287⟩,
⟨128,442916750,442917001⟩]
theorem checked28629 : checkPrefixCuts (2^48) 3756392449 9 Manual.Count131072.C028629.packed 128 cuts28629 = true := by
 decide +kernel
def pointBounds28629 : List (Nat × Nat × Nat) := [(3756418048,104632147754101,104632530741321)]
theorem point_links_checked28629 : (cuts28629.take 1).map (fun c => (3756392449-1+2*2^9*c.k,104632060982863+c.lower,104632443970034+c.upper)) = pointBounds28629 := by
 decide +kernel
def cuts28630 : List PrefixCut := [⟨12,42784745,42784768⟩,
⟨127,449495075,449495328⟩,
⟨128,452866791,452867046⟩]
theorem checked28630 : checkPrefixCuts (2^48) 3756523521 9 Manual.Count131072.C028630.packed 128 cuts28630 = true := by
 decide +kernel
def pointBounds28630 : List (Nat × Nat × Nat) := [(3756535808,104632546684358,104632929671803),(3756653568,104632953394688,104633336382363)]
theorem point_links_checked28630 : (cuts28630.take 2).map (fun c => (3756523521-1+2*2^9*c.k,104632503899613+c.lower,104632886887035+c.upper)) = pointBounds28630 := by
 decide +kernel
def cuts28631 : List PrefixCut := [⟨114,404224921,404225148⟩,
⟨128,453600191,453600445⟩]
theorem checked28631 : checkPrefixCuts (2^48) 3756654593 9 Manual.Count131072.C028631.packed 128 cuts28631 = true := by
 decide +kernel
def pointBounds28631 : List (Nat × Nat × Nat) := [(3756771328,104633360991325,104633743979229)]
theorem point_links_checked28631 : (cuts28631.take 1).map (fun c => (3756654593-1+2*2^9*c.k,104632956766404+c.lower,104633339754081+c.upper)) = pointBounds28631 := by
 decide +kernel
def cuts28632 : List PrefixCut := [⟨101,346220884,346221084⟩,
⟨128,439498850,439499102⟩]
theorem checked28632 : checkPrefixCuts (2^48) 3756785665 9 Manual.Count131072.C028632.packed 128 cuts28632 = true := by
 decide +kernel
def pointBounds28632 : List (Nat × Nat × Nat) := [(3756889088,104633756587479,104634139575610)]
theorem point_links_checked28632 : (cuts28632.take 1).map (fun c => (3756785665-1+2*2^9*c.k,104633410366595+c.lower,104633793354526+c.upper)) = pointBounds28632 := by
 decide +kernel
def cuts28633 : List PrefixCut := [⟨88,308674044,308674214⟩,
⟨128,443754039,443754282⟩]
theorem checked28633 : checkPrefixCuts (2^48) 3756916737 9 Manual.Count131072.C028633.packed 128 cuts28633 = true := by
 decide +kernel
def pointBounds28633 : List (Nat × Nat × Nat) := [(3757006848,104634158539489,104634541527842)]
theorem point_links_checked28633 : (cuts28633.take 1).map (fun c => (3756916737-1+2*2^9*c.k,104633849865445+c.lower,104634232853628+c.upper)) = pointBounds28633 := by
 decide +kernel
def cuts28634 : List PrefixCut := [⟨75,258243723,258243868⟩,
⟨128,443438802,443439053⟩]
theorem checked28634 : checkPrefixCuts (2^48) 3757047809 9 Manual.Count131072.C028634.packed 128 cuts28634 = true := by
 decide +kernel
def pointBounds28634 : List (Nat × Nat × Nat) := [(3757124608,104634551863207,104634934851778)]
theorem point_links_checked28634 : (cuts28634.take 1).map (fun c => (3757047809-1+2*2^9*c.k,104634293619484+c.lower,104634676607910+c.upper)) = pointBounds28634 := by
 decide +kernel
def cuts28635 : List PrefixCut := [⟨62,218754465,218754584⟩,
⟨128,447543697,447543943⟩]
theorem checked28635 : checkPrefixCuts (2^48) 3757178881 9 Manual.Count131072.C028635.packed 128 cuts28635 = true := by
 decide +kernel
def pointBounds28635 : List (Nat × Nat × Nat) := [(3757242368,104634955812751,104635338801547)]
theorem point_links_checked28635 : (cuts28635.take 1).map (fun c => (3757178881-1+2*2^9*c.k,104634737058286+c.lower,104635120046963+c.upper)) = pointBounds28635 := by
 decide +kernel
def cuts28636 : List PrefixCut := [⟨49,168480338,168480434⟩,
⟨128,439062970,439063217⟩]
theorem checked28636 : checkPrefixCuts (2^48) 3757309953 9 Manual.Count131072.C028636.packed 128 cuts28636 = true := by
 decide +kernel
def pointBounds28636 : List (Nat × Nat × Nat) := [(3757360128,104635353082321,104635736071340)]
theorem point_links_checked28636 : (cuts28636.take 1).map (fun c => (3757309953-1+2*2^9*c.k,104635184601983+c.lower,104635567590906+c.upper)) = pointBounds28636 := by
 decide +kernel
def cuts28637 : List PrefixCut := [⟨36,124202378,124202450⟩,
⟨128,443841868,443842123⟩]
theorem checked28637 : checkPrefixCuts (2^48) 3757441025 9 Manual.Count131072.C028637.packed 128 cuts28637 = true := by
 decide +kernel
def pointBounds28637 : List (Nat × Nat × Nat) := [(3757477888,104635747867331,104636130856573)]
theorem point_links_checked28637 : (cuts28637.take 1).map (fun c => (3757441025-1+2*2^9*c.k,104635623664953+c.lower,104636006654123+c.upper)) = pointBounds28637 := by
 decide +kernel
def cuts28638 : List PrefixCut := [⟨23,81275696,81275740⟩,
⟨128,448470695,448470945⟩]
theorem checked28638 : checkPrefixCuts (2^48) 3757572097 9 Manual.Count131072.C028638.packed 128 cuts28638 = true := by
 decide +kernel
def pointBounds28638 : List (Nat × Nat × Nat) := [(3757595648,104636148782517,104636531771986)]
theorem point_links_checked28638 : (cuts28638.take 1).map (fun c => (3757572097-1+2*2^9*c.k,104636067506821+c.lower,104636450496246+c.upper)) = pointBounds28638 := by
 decide +kernel
def cuts28639 : List PrefixCut := [⟨10,35056007,35056027⟩,
⟨125,436320643,436320892⟩,
⟨128,446507521,446507776⟩]
theorem checked28639 : checkPrefixCuts (2^48) 3757703169 9 Manual.Count131072.C028639.packed 128 cuts28639 = true := by
 decide +kernel
def pointBounds28639 : List (Nat × Nat × Nat) := [(3757713408,104636551033523,104636934023218),(3757831168,104636952298159,104637335288083)]
theorem point_links_checked28639 : (cuts28639.take 2).map (fun c => (3757703169-1+2*2^9*c.k,104636515977516+c.lower,104636898967191+c.upper)) = pointBounds28639 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000269
