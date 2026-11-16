import PlattAssemblyKernel
import PlattCertificates.Count131072.C023488
import PlattCertificates.Count131072.C023489
import PlattCertificates.Count131072.C023490
import PlattCertificates.Count131072.C023491
import PlattCertificates.Count131072.C023492
import PlattCertificates.Count131072.C023493
import PlattCertificates.Count131072.C023494
import PlattCertificates.Count131072.C023495
import PlattCertificates.Count131072.C023496
import PlattCertificates.Count131072.C023497
import PlattCertificates.Count131072.C023498
import PlattCertificates.Count131072.C023499
import PlattCertificates.Count131072.C023500
import PlattCertificates.Count131072.C023501
import PlattCertificates.Count131072.C023502
import PlattCertificates.Count131072.C023503
import PlattCertificates.Count131072.C023504
import PlattCertificates.Count131072.C023505
import PlattCertificates.Count131072.C023506
import PlattCertificates.Count131072.C023507
import PlattCertificates.Count131072.C023508
import PlattCertificates.Count131072.C023509
import PlattCertificates.Count131072.C023510
import PlattCertificates.Count131072.C023511
import PlattCertificates.Count131072.C023512
import PlattCertificates.Count131072.C023513
import PlattCertificates.Count131072.C023514
import PlattCertificates.Count131072.C023515
import PlattCertificates.Count131072.C023516
import PlattCertificates.Count131072.C023517
import PlattCertificates.Count131072.C023518
import PlattCertificates.Count131072.C023519
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000109
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23488 : List PrefixCut := [⟨24,103547750,103547807⟩,
⟨119,505221049,505221330⟩,
⟨128,541653169,541653471⟩]
theorem checked23488 : checkPrefixCuts (2^48) 3082551297 9 Manual.Count131072.C023488.packed 128 cuts23488 = true := by
 decide +kernel
def pointBounds23488 : List (Nat × Nat × Nat) := [(3082575872,102096640838041,102097022402670),(3082673152,102097042511340,102097424076193)]
theorem point_links_checked23488 : (cuts23488.take 2).map (fun c => (3082551297-1+2*2^9*c.k,102096537290291+c.lower,102096918854863+c.upper)) = pointBounds23488 := by
 decide +kernel
def cuts23489 : List PrefixCut := [⟨86,366232882,366233094⟩,
⟨128,548843267,548843579⟩]
theorem checked23489 : checkPrefixCuts (2^48) 3082682369 9 Manual.Count131072.C023489.packed 128 cuts23489 = true := by
 decide +kernel
def pointBounds23489 : List (Nat × Nat × Nat) := [(3082770432,102097445176342,102097826741428)]
theorem point_links_checked23489 : (cuts23489.take 1).map (fun c => (3082682369-1+2*2^9*c.k,102097078943460+c.lower,102097460508334+c.upper)) = pointBounds23489 := by
 decide +kernel
def cuts23490 : List PrefixCut := [⟨53,230724553,230724681⟩,
⟨128,555850279,555850590⟩]
theorem checked23490 : checkPrefixCuts (2^48) 3082813441 9 Manual.Count131072.C023490.packed 128 cuts23490 = true := by
 decide +kernel
def pointBounds23490 : List (Nat × Nat × Nat) := [(3082867712,102097858511280,102098240076594)]
theorem point_links_checked23490 : (cuts23490.take 1).map (fun c => (3082813441-1+2*2^9*c.k,102097627786727+c.lower,102098009351913+c.upper)) = pointBounds23490 := by
 decide +kernel
def cuts23491 : List PrefixCut := [⟨20,85274545,85274589⟩,
⟨115,491096897,491097172⟩,
⟨128,545966384,545966692⟩]
theorem checked23491 : checkPrefixCuts (2^48) 3082944513 9 Manual.Count131072.C023491.packed 128 cuts23491 = true := by
 decide +kernel
def pointBounds23491 : List (Nat × Nat × Nat) := [(3082964992,102098268911551,102098650477092),(3083062272,102098674733903,102099056299675)]
theorem point_links_checked23491 : (cuts23491.take 2).map (fun c => (3082944513-1+2*2^9*c.k,102098183637006+c.lower,102098565202503+c.upper)) = pointBounds23491 := by
 decide +kernel
def cuts23492 : List PrefixCut := [⟨82,351305260,351305461⟩,
⟨128,549321050,549321364⟩]
theorem checked23492 : checkPrefixCuts (2^48) 3083075585 9 Manual.Count131072.C023492.packed 128 cuts23492 = true := by
 decide +kernel
def pointBounds23492 : List (Nat × Nat × Nat) := [(3083159552,102099080908650,102099462474656)]
theorem point_links_checked23492 : (cuts23492.take 1).map (fun c => (3083075585-1+2*2^9*c.k,102098729603390+c.lower,102099111169195+c.upper)) = pointBounds23492 := by
 decide +kernel
def cuts23493 : List PrefixCut := [⟨49,208146147,208146260⟩,
⟨128,547654474,547654777⟩]
theorem checked23493 : checkPrefixCuts (2^48) 3083206657 9 Manual.Count131072.C023493.packed 128 cuts23493 = true := by
 decide +kernel
def pointBounds23493 : List (Nat × Nat × Nat) := [(3083256832,102099487070587,102099868636819)]
theorem point_links_checked23493 : (cuts23493.take 1).map (fun c => (3083206657-1+2*2^9*c.k,102099278924440+c.lower,102099660490559+c.upper)) = pointBounds23493 := by
 decide +kernel
def cuts23494 : List PrefixCut := [⟨16,64449881,64449920⟩,
⟨111,474237599,474237872⟩,
⟨128,544618646,544618956⟩]
theorem checked23494 : checkPrefixCuts (2^48) 3083337729 9 Manual.Count131072.C023494.packed 128 cuts23494 = true := by
 decide +kernel
def pointBounds23494 : List (Nat × Nat × Nat) := [(3083354112,102099891028795,102100272595256),(3083451392,102100300816513,102100682383208)]
theorem point_links_checked23494 : (cuts23494.take 2).map (fun c => (3083337729-1+2*2^9*c.k,102099826578914+c.lower,102100208145336+c.upper)) = pointBounds23494 := by
 decide +kernel
def cuts23495 : List PrefixCut := [⟨78,331269464,331269653⟩,
⟨128,541765794,541766107⟩]
theorem checked23495 : checkPrefixCuts (2^48) 3083468801 9 Manual.Count131072.C023495.packed 128 cuts23495 = true := by
 decide +kernel
def pointBounds23495 : List (Nat × Nat × Nat) := [(3083548672,102100702467024,102101084033945)]
theorem point_links_checked23495 : (cuts23495.take 1).map (fun c => (3083468801-1+2*2^9*c.k,102100371197560+c.lower,102100752764292+c.upper)) = pointBounds23495 := by
 decide +kernel
def cuts23496 : List PrefixCut := [⟨45,194336355,194336465⟩,
⟨128,549227663,549227973⟩]
theorem checked23496 : checkPrefixCuts (2^48) 3083599873 9 Manual.Count131072.C023496.packed 128 cuts23496 = true := by
 decide +kernel
def pointBounds23496 : List (Nat × Nat × Nat) := [(3083645952,102101107299709,102101488866864)]
theorem point_links_checked23496 : (cuts23496.take 1).map (fun c => (3083599873-1+2*2^9*c.k,102100912963354+c.lower,102101294530399+c.upper)) = pointBounds23496 := by
 decide +kernel
def cuts23497 : List PrefixCut := [⟨12,50750124,50750151⟩,
⟨107,457747893,457748154⟩,
⟨128,547013693,547014005⟩]
theorem checked23497 : checkPrefixCuts (2^48) 3083730945 9 Manual.Count131072.C023497.packed 128 cuts23497 = true := by
 decide +kernel
def pointBounds23497 : List (Nat × Nat × Nat) := [(3083743232,102101512941141,102101894508523),(3083840512,102101919938910,102102301506526)]
theorem point_links_checked23497 : (cuts23497.take 2).map (fun c => (3083730945-1+2*2^9*c.k,102101462191017+c.lower,102101843758372+c.upper)) = pointBounds23497 := by
 decide +kernel
def cuts23498 : List PrefixCut := [⟨74,314889688,314889874⟩,
⟨128,545895160,545895479⟩]
theorem checked23498 : checkPrefixCuts (2^48) 3083862017 9 Manual.Count131072.C023498.packed 128 cuts23498 = true := by
 decide +kernel
def pointBounds23498 : List (Nat × Nat × Nat) := [(3083937792,102102324094398,102102705662251)]
theorem point_links_checked23498 : (cuts23498.take 1).map (fun c => (3083862017-1+2*2^9*c.k,102102009204710+c.lower,102102390772377+c.upper)) = pointBounds23498 := by
 decide +kernel
def cuts23499 : List PrefixCut := [⟨41,176879336,176879432⟩,
⟨128,548701352,548701642⟩]
theorem checked23499 : checkPrefixCuts (2^48) 3083993089 9 Manual.Count131072.C023499.packed 128 cuts23499 = true := by
 decide +kernel
def pointBounds23499 : List (Nat × Nat × Nat) := [(3084035072,102102731979206,102103113547288)]
theorem point_links_checked23499 : (cuts23499.take 1).map (fun c => (3083993089-1+2*2^9*c.k,102102555099870+c.lower,102102936667856+c.upper)) = pointBounds23499 := by
 decide +kernel
def cuts23500 : List PrefixCut := [⟨8,33038157,33038175⟩,
⟨103,440806023,440806271⟩,
⟨128,546396446,546396755⟩]
theorem checked23500 : checkPrefixCuts (2^48) 3084124161 9 Manual.Count131072.C023500.packed 128 cuts23500 = true := by
 decide +kernel
def pointBounds23500 : List (Nat × Nat × Nat) := [(3084132352,102103136839379,102103518407673),(3084229632,102103544607245,102103926175769)]
theorem point_links_checked23500 : (cuts23500.take 2).map (fun c => (3084124161-1+2*2^9*c.k,102103103801222+c.lower,102103485369498+c.upper)) = pointBounds23500 := by
 decide +kernel
def cuts23501 : List PrefixCut := [⟨70,302803346,302803517⟩,
⟨128,551666283,551666597⟩]
theorem checked23501 : checkPrefixCuts (2^48) 3084255233 9 Manual.Count131072.C023501.packed 128 cuts23501 = true := by
 decide +kernel
def pointBounds23501 : List (Nat × Nat × Nat) := [(3084326912,102103953001014,102104334569770)]
theorem point_links_checked23501 : (cuts23501.take 1).map (fun c => (3084255233-1+2*2^9*c.k,102103650197668+c.lower,102104031766253+c.upper)) = pointBounds23501 := by
 decide +kernel
def cuts23502 : List PrefixCut := [⟨37,158331625,158331716⟩,
⟨128,550730314,550730622⟩]
theorem checked23502 : checkPrefixCuts (2^48) 3084386305 9 Manual.Count131072.C023502.packed 128 cuts23502 = true := by
 decide +kernel
def pointBounds23502 : List (Nat × Nat × Nat) := [(3084424192,102104360195576,102104741764566)]
theorem point_links_checked23502 : (cuts23502.take 1).map (fun c => (3084386305-1+2*2^9*c.k,102104201863951+c.lower,102104583432850+c.upper)) = pointBounds23502 := by
 decide +kernel
def cuts23503 : List PrefixCut := [⟨4,16334477,16334485⟩,
⟨99,421952084,421952330⟩,
⟨128,545779244,545779559⟩]
theorem checked23503 : checkPrefixCuts (2^48) 3084517377 9 Manual.Count131072.C023503.packed 128 cuts23503 = true := by
 decide +kernel
def pointBounds23503 : List (Nat × Nat × Nat) := [(3084521472,102104768928742,102105150497957),(3084618752,102105174546349,102105556115802)]
theorem point_links_checked23503 : (cuts23503.take 2).map (fun c => (3084517377-1+2*2^9*c.k,102104752594265+c.lower,102105134163472+c.upper)) = pointBounds23503 := by
 decide +kernel
def cuts23504 : List PrefixCut := [⟨66,279861408,279861559⟩,
⟨128,546577255,546577557⟩]
theorem checked23504 : checkPrefixCuts (2^48) 3084648449 9 Manual.Count131072.C023504.packed 128 cuts23504 = true := by
 decide +kernel
def pointBounds23504 : List (Nat × Nat × Nat) := [(3084716032,102105578234917,102105959804590)]
theorem point_links_checked23504 : (cuts23504.take 1).map (fun c => (3084648449-1+2*2^9*c.k,102105298373509+c.lower,102105679943031+c.upper)) = pointBounds23504 := by
 decide +kernel
def cuts23505 : List PrefixCut := [⟨33,141248584,141248664⟩,
⟨128,550112557,550112865⟩]
theorem checked23505 : checkPrefixCuts (2^48) 3084779521 9 Manual.Count131072.C023505.packed 128 cuts23505 = true := by
 decide +kernel
def pointBounds23505 : List (Nat × Nat × Nat) := [(3084813312,102105986199348,102106367769252),(3084910592,102106395063321,102106776633453)]
theorem point_links_checked23505 : (cuts23505.take 2).map (fun c => (3084779521-1+2*2^9*c.k,102105844950764+c.lower,102106226520588+c.upper)) = pointBounds23505 := by
 decide +kernel
def cuts23506 : List PrefixCut := [⟨95,404380263,404380501⟩,
⟨128,548264330,548264647⟩]
theorem checked23506 : checkPrefixCuts (2^48) 3084910593 9 Manual.Count131072.C023506.packed 128 cuts23506 = true := by
 decide +kernel
def pointBounds23506 : List (Nat × Nat × Nat) := [(3085007872,102106799443584,102107181013954)]
theorem point_links_checked23506 : (cuts23506.take 1).map (fun c => (3084910593-1+2*2^9*c.k,102106395063321+c.lower,102106776633453+c.upper)) = pointBounds23506 := by
 decide +kernel
def cuts23507 : List PrefixCut := [⟨62,260483525,260483671⟩,
⟨128,545868909,545869216⟩]
theorem checked23507 : checkPrefixCuts (2^48) 3085041665 9 Manual.Count131072.C023507.packed 128 cuts23507 = true := by
 decide +kernel
def pointBounds23507 : List (Nat × Nat × Nat) := [(3085105152,102107203811176,102107585381771)]
theorem point_links_checked23507 : (cuts23507.take 1).map (fun c => (3085041665-1+2*2^9*c.k,102106943327651+c.lower,102107324898100+c.upper)) = pointBounds23507 := by
 decide +kernel
def cuts23508 : List PrefixCut := [⟨29,125629615,125629683⟩,
⟨124,532526172,532526469⟩,
⟨128,549130199,549130505⟩]
theorem checked23508 : checkPrefixCuts (2^48) 3085172737 9 Manual.Count131072.C023508.packed 128 cuts23508 = true := by
 decide +kernel
def pointBounds23508 : List (Nat × Nat × Nat) := [(3085202432,102107614826175,102107996396999),(3085299712,102108021722732,102108403293785)]
theorem point_links_checked23508 : (cuts23508.take 2).map (fun c => (3085172737-1+2*2^9*c.k,102107489196560+c.lower,102107870767316+c.upper)) = pointBounds23508 := by
 decide +kernel
def cuts23509 : List PrefixCut := [⟨91,385535761,385535979⟩,
⟨128,543176958,543177259⟩]
theorem checked23509 : checkPrefixCuts (2^48) 3085303809 9 Manual.Count131072.C023509.packed 128 cuts23509 = true := by
 decide +kernel
def pointBounds23509 : List (Nat × Nat × Nat) := [(3085396992,102108423862520,102108805433800)]
theorem point_links_checked23509 : (cuts23509.take 1).map (fun c => (3085303809-1+2*2^9*c.k,102108038326759+c.lower,102108419897821+c.upper)) = pointBounds23509 := by
 decide +kernel
def cuts23510 : List PrefixCut := [⟨58,251966469,251966610⟩,
⟨128,549448497,549448804⟩]
theorem checked23510 : checkPrefixCuts (2^48) 3085434881 9 Manual.Count131072.C023510.packed 128 cuts23510 = true := by
 decide +kernel
def pointBounds23510 : List (Nat × Nat × Nat) := [(3085494272,102108833470186,102109215041690)]
theorem point_links_checked23510 : (cuts23510.take 1).map (fun c => (3085434881-1+2*2^9*c.k,102108581503717+c.lower,102108963075080+c.upper)) = pointBounds23510 := by
 decide +kernel
def cuts23511 : List PrefixCut := [⟨25,109558497,109558557⟩,
⟨120,517589598,517589887⟩,
⟨128,552800270,552800578⟩]
theorem checked23511 : checkPrefixCuts (2^48) 3085565953 9 Manual.Count131072.C023511.packed 128 cuts23511 = true := by
 decide +kernel
def pointBounds23511 : List (Nat × Nat × Nat) := [(3085591552,102109240510711,102109622082441),(3085688832,102109648541812,102110030113771)]
theorem point_links_checked23511 : (cuts23511.take 2).map (fun c => (3085565953-1+2*2^9*c.k,102109130952214+c.lower,102109512523884+c.upper)) = pointBounds23511 := by
 decide +kernel
def cuts23512 : List PrefixCut := [⟨87,374084664,374084878⟩,
⟨128,548580821,548581136⟩]
theorem checked23512 : checkPrefixCuts (2^48) 3085697025 9 Manual.Count131072.C023512.packed 128 cuts23512 = true := by
 decide +kernel
def pointBounds23512 : List (Nat × Nat × Nat) := [(3085786112,102110057837148,102110439409340)]
theorem point_links_checked23512 : (cuts23512.take 1).map (fun c => (3085697025-1+2*2^9*c.k,102109683752484+c.lower,102110065324462+c.upper)) = pointBounds23512 := by
 decide +kernel
def cuts23513 : List PrefixCut := [⟨54,229769406,229769535⟩,
⟨128,547827748,547828056⟩]
theorem checked23513 : checkPrefixCuts (2^48) 3085828097 9 Manual.Count131072.C023513.packed 128 cuts23513 = true := by
 decide +kernel
def pointBounds23513 : List (Nat × Nat × Nat) := [(3085883392,102110462102711,102110843675133)]
theorem point_links_checked23513 : (cuts23513.take 1).map (fun c => (3085828097-1+2*2^9*c.k,102110232333305+c.lower,102110613905598+c.upper)) = pointBounds23513 := by
 decide +kernel
def cuts23514 : List PrefixCut := [⟨21,89386938,89386987⟩,
⟨116,497549050,497549325⟩,
⟨128,545159512,545159817⟩]
theorem checked23514 : checkPrefixCuts (2^48) 3085959169 9 Manual.Count131072.C023514.packed 128 cuts23514 = true := by
 decide +kernel
def pointBounds23514 : List (Nat × Nat × Nat) := [(3085980672,102110869547991,102111251120641),(3086077952,102111277710103,102111659282979)]
theorem point_links_checked23514 : (cuts23514.take 2).map (fun c => (3085959169-1+2*2^9*c.k,102110780161053+c.lower,102111161733654+c.upper)) = pointBounds23514 := by
 decide +kernel
def cuts23515 : List PrefixCut := [⟨83,354154269,354154465⟩,
⟨128,544953889,544954190⟩]
theorem checked23515 : checkPrefixCuts (2^48) 3086090241 9 Manual.Count131072.C023515.packed 128 cuts23515 = true := by
 decide +kernel
def pointBounds23515 : List (Nat × Nat × Nat) := [(3086175232,102111679474834,102112061047936)]
theorem point_links_checked23515 : (cuts23515.take 1).map (fun c => (3086090241-1+2*2^9*c.k,102111325320565+c.lower,102111706893471+c.upper)) = pointBounds23515 := by
 decide +kernel
def cuts23516 : List PrefixCut := [⟨50,208216373,208216496⟩,
⟨128,540370546,540370852⟩]
theorem checked23516 : checkPrefixCuts (2^48) 3086221313 9 Manual.Count131072.C023516.packed 128 cuts23516 = true := by
 decide +kernel
def pointBounds23516 : List (Nat × Nat × Nat) := [(3086272512,102112078490827,102112460064157)]
theorem point_links_checked23516 : (cuts23516.take 1).map (fun c => (3086221313-1+2*2^9*c.k,102111870274454+c.lower,102112251847661+c.upper)) = pointBounds23516 := by
 decide +kernel
def cuts23517 : List PrefixCut := [⟨17,73324481,73324523⟩,
⟨112,480340763,480341043⟩,
⟨128,550744247,550744566⟩]
theorem checked23517 : checkPrefixCuts (2^48) 3086352385 9 Manual.Count131072.C023517.packed 128 cuts23517 = true := by
 decide +kernel
def pointBounds23517 : List (Nat × Nat × Nat) := [(3086369792,102112483969481,102112865543036),(3086467072,102112890985763,102113272559556)]
theorem point_links_checked23517 : (cuts23517.take 2).map (fun c => (3086352385-1+2*2^9*c.k,102112410645000+c.lower,102112792218513+c.upper)) = pointBounds23517 := by
 decide +kernel
def cuts23518 : List PrefixCut := [⟨79,335596818,335597006⟩,
⟨128,541510261,541510563⟩]
theorem checked23518 : checkPrefixCuts (2^48) 3086483457 9 Manual.Count131072.C023518.packed 128 cuts23518 = true := by
 decide +kernel
def pointBounds23518 : List (Nat × Nat × Nat) := [(3086564352,102113296986065,102113678560085)]
theorem point_links_checked23518 : (cuts23518.take 1).map (fun c => (3086483457-1+2*2^9*c.k,102112961389247+c.lower,102113342963079+c.upper)) = pointBounds23518 := by
 decide +kernel
def cuts23519 : List PrefixCut := [⟨46,198250132,198250249⟩,
⟨128,550515050,550515360⟩]
theorem checked23519 : checkPrefixCuts (2^48) 3086614529 9 Manual.Count131072.C023519.packed 128 cuts23519 = true := by
 decide +kernel
def pointBounds23519 : List (Nat × Nat × Nat) := [(3086661632,102113701149640,102114082723891)]
theorem point_links_checked23519 : (cuts23519.take 1).map (fun c => (3086614529-1+2*2^9*c.k,102113502899508+c.lower,102113884473642+c.upper)) = pointBounds23519 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000109
