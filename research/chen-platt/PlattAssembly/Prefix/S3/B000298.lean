import PlattAssemblyKernel
import PlattCertificates.Count131072.C029536
import PlattCertificates.Count131072.C029537
import PlattCertificates.Count131072.C029538
import PlattCertificates.Count131072.C029539
import PlattCertificates.Count131072.C029540
import PlattCertificates.Count131072.C029541
import PlattCertificates.Count131072.C029542
import PlattCertificates.Count131072.C029543
import PlattCertificates.Count131072.C029544
import PlattCertificates.Count131072.C029545
import PlattCertificates.Count131072.C029546
import PlattCertificates.Count131072.C029547
import PlattCertificates.Count131072.C029548
import PlattCertificates.Count131072.C029549
import PlattCertificates.Count131072.C029550
import PlattCertificates.Count131072.C029551
import PlattCertificates.Count131072.C029552
import PlattCertificates.Count131072.C029553
import PlattCertificates.Count131072.C029554
import PlattCertificates.Count131072.C029555
import PlattCertificates.Count131072.C029556
import PlattCertificates.Count131072.C029557
import PlattCertificates.Count131072.C029558
import PlattCertificates.Count131072.C029559
import PlattCertificates.Count131072.C029560
import PlattCertificates.Count131072.C029561
import PlattCertificates.Count131072.C029562
import PlattCertificates.Count131072.C029563
import PlattCertificates.Count131072.C029564
import PlattCertificates.Count131072.C029565
import PlattCertificates.Count131072.C029566
import PlattCertificates.Count131072.C029567
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000298
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts29536 : List PrefixCut := [⟨43,145629397,145629479⟩,
⟨128,433614892,433615132⟩]
theorem checked29536 : checkPrefixCuts (2^48) 3875274753 9 Manual.Count131072.C029536.packed 128 cuts29536 = true := by
 decide +kernel
def pointBounds29536 : List (Nat × Nat × Nat) := [(3875318784,105029696400850,105030079610832)]
theorem point_links_checked29536 : (cuts29536.take 1).map (fun c => (3875274753-1+2*2^9*c.k,105029550771453+c.lower,105029933981353+c.upper)) = pointBounds29536 := by
 decide +kernel
def cuts29537 : List PrefixCut := [⟨34,114320802,114320868⟩,
⟨128,434399067,434399304⟩]
theorem checked29537 : checkPrefixCuts (2^48) 3875405825 9 Manual.Count131072.C029537.packed 128 cuts29537 = true := by
 decide +kernel
def pointBounds29537 : List (Nat × Nat × Nat) := [(3875440640,105030098707147,105030481917353)]
theorem point_links_checked29537 : (cuts29537.take 1).map (fun c => (3875405825-1+2*2^9*c.k,105029984386345+c.lower,105030367596485+c.upper)) = pointBounds29537 := by
 decide +kernel
def cuts29538 : List PrefixCut := [⟨25,83522634,83522684⟩,
⟨128,428864712,428864960⟩]
theorem checked29538 : checkPrefixCuts (2^48) 3875536897 9 Manual.Count131072.C029538.packed 128 cuts29538 = true := by
 decide +kernel
def pointBounds29538 : List (Nat × Nat × Nat) := [(3875562496,105030502308046,105030885518473)]
theorem point_links_checked29538 : (cuts29538.take 1).map (fun c => (3875536897-1+2*2^9*c.k,105030418785412+c.lower,105030801995789+c.upper)) = pointBounds29538 := by
 decide +kernel
def cuts29539 : List PrefixCut := [⟨16,52508605,52508637⟩,
⟨128,427542974,427543218⟩]
theorem checked29539 : checkPrefixCuts (2^48) 3875667969 9 Manual.Count131072.C029539.packed 128 cuts29539 = true := by
 decide +kernel
def pointBounds29539 : List (Nat × Nat × Nat) := [(3875684352,105030900158729,105031283369386)]
theorem point_links_checked29539 : (cuts29539.take 1).map (fun c => (3875667969-1+2*2^9*c.k,105030847650124+c.lower,105031230860749+c.upper)) = pointBounds29539 := by
 decide +kernel
def cuts29540 : List PrefixCut := [⟨7,24038428,24038439⟩,
⟨126,422590312,422590541⟩,
⟨128,429489333,429489565⟩]
theorem checked29540 : checkPrefixCuts (2^48) 3875799041 9 Manual.Count131072.C029540.packed 128 cuts29540 = true := by
 decide +kernel
def pointBounds29540 : List (Nat × Nat × Nat) := [(3875806208,105031299231526,105031682442406),(3875928064,105031697783410,105032080994508)]
theorem point_links_checked29540 : (cuts29540.take 2).map (fun c => (3875799041-1+2*2^9*c.k,105031275193098+c.lower,105031658403967+c.upper)) = pointBounds29540 := by
 decide +kernel
def cuts29541 : List PrefixCut := [⟨117,396651178,396651396⟩,
⟨128,434848720,434848960⟩]
theorem checked29541 : checkPrefixCuts (2^48) 3875930113 9 Manual.Count131072.C029541.packed 128 cuts29541 = true := by
 decide +kernel
def pointBounds29541 : List (Nat × Nat × Nat) := [(3876049920,105032101333609,105032484544928)]
theorem point_links_checked29541 : (cuts29541.take 1).map (fun c => (3875930113-1+2*2^9*c.k,105031704682431+c.lower,105032087893532+c.upper)) = pointBounds29541 := by
 decide +kernel
def cuts29542 : List PrefixCut := [⟨108,363669692,363669899⟩,
⟨128,432001846,432002090⟩]
theorem checked29542 : checkPrefixCuts (2^48) 3876061185 9 Manual.Count131072.C029542.packed 128 cuts29542 = true := by
 decide +kernel
def pointBounds29542 : List (Nat × Nat × Nat) := [(3876171776,105032503200843,105032886412391)]
theorem point_links_checked29542 : (cuts29542.take 1).map (fun c => (3876061185-1+2*2^9*c.k,105032139531151+c.lower,105032522742492+c.upper)) = pointBounds29542 := by
 decide +kernel
def cuts29543 : List PrefixCut := [⟨99,335120032,335120216⟩,
⟨128,433294369,433294612⟩]
theorem checked29543 : checkPrefixCuts (2^48) 3876192257 9 Manual.Count131072.C029543.packed 128 cuts29543 = true := by
 decide +kernel
def pointBounds29543 : List (Nat × Nat × Nat) := [(3876293632,105032906653029,105033289864798)]
theorem point_links_checked29543 : (cuts29543.take 1).map (fun c => (3876192257-1+2*2^9*c.k,105032571532997+c.lower,105032954744582+c.upper)) = pointBounds29543 := by
 decide +kernel
def cuts29544 : List PrefixCut := [⟨90,299891752,299891922⟩,
⟨128,429866871,429867112⟩]
theorem checked29544 : checkPrefixCuts (2^48) 3876323329 9 Manual.Count131072.C029544.packed 128 cuts29544 = true := by
 decide +kernel
def pointBounds29544 : List (Nat × Nat × Nat) := [(3876415488,105033304719118,105033687931116)]
theorem point_links_checked29544 : (cuts29544.take 1).map (fun c => (3876323329-1+2*2^9*c.k,105033004827366+c.lower,105033388039194+c.upper)) = pointBounds29544 := by
 decide +kernel
def cuts29545 : List PrefixCut := [⟨81,271491219,271491368⟩,
⟨128,427891931,427892167⟩]
theorem checked29545 : checkPrefixCuts (2^48) 3876454401 9 Manual.Count131072.C029545.packed 128 cuts29545 = true := by
 decide +kernel
def pointBounds29545 : List (Nat × Nat × Nat) := [(3876537344,105033706185456,105034089397674)]
theorem point_links_checked29545 : (cuts29545.take 1).map (fun c => (3876454401-1+2*2^9*c.k,105033434694237+c.lower,105033817906306+c.upper)) = pointBounds29545 := by
 decide +kernel
def cuts29546 : List PrefixCut := [⟨72,245052917,245053054⟩,
⟨128,432379104,432379347⟩]
theorem checked29546 : checkPrefixCuts (2^48) 3876585473 9 Manual.Count131072.C029546.packed 128 cuts29546 = true := by
 decide +kernel
def pointBounds29546 : List (Nat × Nat × Nat) := [(3876659200,105034107639085,105034490851527)]
theorem point_links_checked29546 : (cuts29546.take 1).map (fun c => (3876585473-1+2*2^9*c.k,105033862586168+c.lower,105034245798473+c.upper)) = pointBounds29546 := by
 decide +kernel
def cuts29547 : List PrefixCut := [⟨63,209685882,209686000⟩,
⟨128,430186311,430186549⟩]
theorem checked29547 : checkPrefixCuts (2^48) 3876716545 9 Manual.Count131072.C029547.packed 128 cuts29547 = true := by
 decide +kernel
def pointBounds29547 : List (Nat × Nat × Nat) := [(3876781056,105034504651154,105034887863820)]
theorem point_links_checked29547 : (cuts29547.take 1).map (fun c => (3876716545-1+2*2^9*c.k,105034294965272+c.lower,105034678177820+c.upper)) = pointBounds29547 := by
 decide +kernel
def cuts29548 : List PrefixCut := [⟨54,182452703,182452808⟩,
⟨128,435907402,435907652⟩]
theorem checked29548 : checkPrefixCuts (2^48) 3876847617 9 Manual.Count131072.C029548.packed 128 cuts29548 = true := by
 decide +kernel
def pointBounds29548 : List (Nat × Nat × Nat) := [(3876902912,105034907604286,105035290817177)]
theorem point_links_checked29548 : (cuts29548.take 1).map (fun c => (3876847617-1+2*2^9*c.k,105034725151583+c.lower,105035108364369+c.upper)) = pointBounds29548 := by
 decide +kernel
def cuts29549 : List PrefixCut := [⟨45,152607690,152607776⟩,
⟨128,430810701,430810939⟩]
theorem checked29549 : checkPrefixCuts (2^48) 3876978689 9 Manual.Count131072.C029549.packed 128 cuts29549 = true := by
 decide +kernel
def pointBounds29549 : List (Nat × Nat × Nat) := [(3877024768,105035313666675,105035696879797)]
theorem point_links_checked29549 : (cuts29549.take 1).map (fun c => (3876978689-1+2*2^9*c.k,105035161058985+c.lower,105035544272021+c.upper)) = pointBounds29549 := by
 decide +kernel
def cuts29550 : List PrefixCut := [⟨36,122111209,122111275⟩,
⟨128,429707175,429707415⟩]
theorem checked29550 : checkPrefixCuts (2^48) 3877109761 9 Manual.Count131072.C029550.packed 128 cuts29550 = true := by
 decide +kernel
def pointBounds29550 : List (Nat × Nat × Nat) := [(3877146624,105035713980895,105036097194235)]
theorem point_links_checked29550 : (cuts29550.take 1).map (fun c => (3877109761-1+2*2^9*c.k,105035591869686+c.lower,105035975082960+c.upper)) = pointBounds29550 := by
 decide +kernel
def cuts29551 : List PrefixCut := [⟨27,91253728,91253777⟩,
⟨128,434701710,434701948⟩]
theorem checked29551 : checkPrefixCuts (2^48) 3877240833 9 Manual.Count131072.C029551.packed 128 cuts29551 = true := by
 decide +kernel
def pointBounds29551 : List (Nat × Nat × Nat) := [(3877268480,105036112830589,105036496044152)]
theorem point_links_checked29551 : (cuts29551.take 1).map (fun c => (3877240833-1+2*2^9*c.k,105036021576861+c.lower,105036404790375+c.upper)) = pointBounds29551 := by
 decide +kernel
def cuts29552 : List PrefixCut := [⟨18,61995346,61995381⟩,
⟨128,435122535,435122775⟩]
theorem checked29552 : checkPrefixCuts (2^48) 3877371905 9 Manual.Count131072.C029552.packed 128 cuts29552 = true := by
 decide +kernel
def pointBounds29552 : List (Nat × Nat × Nat) := [(3877390336,105036518273917,105036901487704)]
theorem point_links_checked29552 : (cuts29552.take 1).map (fun c => (3877371905-1+2*2^9*c.k,105036456278571+c.lower,105036839492323+c.upper)) = pointBounds29552 := by
 decide +kernel
def cuts29553 : List PrefixCut := [⟨9,30052967,30052985⟩,
⟨128,426905144,426905391⟩]
theorem checked29553 : checkPrefixCuts (2^48) 3877502977 9 Manual.Count131072.C029553.packed 128 cuts29553 = true := by
 decide +kernel
def pointBounds29553 : List (Nat × Nat × Nat) := [(3877512192,105036921454073,105037304668083),(3877634048,105037318306250,105037701520489)]
theorem point_links_checked29553 : (cuts29553.take 2).map (fun c => (3877502977-1+2*2^9*c.k,105036891401106+c.lower,105037274615098+c.upper)) = pointBounds29553 := by
 decide +kernel
def cuts29554 : List PrefixCut := [⟨119,404534001,404534228⟩,
⟨128,432117049,432117293⟩]
theorem checked29554 : checkPrefixCuts (2^48) 3877634049 9 Manual.Count131072.C029554.packed 128 cuts29554 = true := by
 decide +kernel
def pointBounds29554 : List (Nat × Nat × Nat) := [(3877755904,105037722840251,105038106054717)]
theorem point_links_checked29554 : (cuts29554.take 1).map (fun c => (3877634049-1+2*2^9*c.k,105037318306250+c.lower,105037701520489+c.upper)) = pointBounds29554 := by
 decide +kernel
def cuts29555 : List PrefixCut := [⟨110,372873383,372873594⟩,
⟨128,433481530,433481775⟩]
theorem checked29555 : checkPrefixCuts (2^48) 3877765121 9 Manual.Count131072.C029555.packed 128 cuts29555 = true := by
 decide +kernel
def pointBounds29555 : List (Nat × Nat × Nat) := [(3877877760,105038123296682,105038506511376)]
theorem point_links_checked29555 : (cuts29555.take 1).map (fun c => (3877765121-1+2*2^9*c.k,105037750423299+c.lower,105038133637782+c.upper)) = pointBounds29555 := by
 decide +kernel
def cuts29556 : List PrefixCut := [⟨101,339690565,339690756⟩,
⟨128,430200615,430200852⟩]
theorem checked29556 : checkPrefixCuts (2^48) 3877896193 9 Manual.Count131072.C029556.packed 128 cuts29556 = true := by
 decide +kernel
def pointBounds29556 : List (Nat × Nat × Nat) := [(3877999616,105038523595394,105038906810313)]
theorem point_links_checked29556 : (cuts29556.take 1).map (fun c => (3877896193-1+2*2^9*c.k,105038183904829+c.lower,105038567119557+c.upper)) = pointBounds29556 := by
 decide +kernel
def cuts29557 : List PrefixCut := [⟨92,303171257,303171434⟩,
⟨128,423436109,423436352⟩]
theorem checked29557 : checkPrefixCuts (2^48) 3878027265 9 Manual.Count131072.C029557.packed 128 cuts29557 = true := by
 decide +kernel
def pointBounds29557 : List (Nat × Nat × Nat) := [(3878121472,105038917276701,105039300491843)]
theorem point_links_checked29557 : (cuts29557.take 1).map (fun c => (3878027265-1+2*2^9*c.k,105038614105444+c.lower,105038997320409+c.upper)) = pointBounds29557 := by
 decide +kernel
def cuts29558 : List PrefixCut := [⟨83,281024860,281025011⟩,
⟨128,433945663,433945899⟩]
theorem checked29558 : checkPrefixCuts (2^48) 3878158337 9 Manual.Count131072.C029558.packed 128 cuts29558 = true := by
 decide +kernel
def pointBounds29558 : List (Nat × Nat × Nat) := [(3878243328,105039318566413,105039701781772)]
theorem point_links_checked29558 : (cuts29558.take 1).map (fun c => (3878158337-1+2*2^9*c.k,105039037541553+c.lower,105039420756761+c.upper)) = pointBounds29558 := by
 decide +kernel
def cuts29559 : List PrefixCut := [⟨74,241243842,241243980⟩,
⟨128,422318806,422319043⟩]
theorem checked29559 : checkPrefixCuts (2^48) 3878289409 9 Manual.Count131072.C029559.packed 128 cuts29559 = true := by
 decide +kernel
def pointBounds29559 : List (Nat × Nat × Nat) := [(3878365184,105039712731058,105040095946640)]
theorem point_links_checked29559 : (cuts29559.take 1).map (fun c => (3878289409-1+2*2^9*c.k,105039471487216+c.lower,105039854702660+c.upper)) = pointBounds29559 := by
 decide +kernel
def cuts29560 : List PrefixCut := [⟨65,217794564,217794688⟩,
⟨128,428763611,428763853⟩]
theorem checked29560 : checkPrefixCuts (2^48) 3878420481 9 Manual.Count131072.C029560.packed 128 cuts29560 = true := by
 decide +kernel
def pointBounds29560 : List (Nat × Nat × Nat) := [(3878487040,105040111600586,105040494816391)]
theorem point_links_checked29560 : (cuts29560.take 1).map (fun c => (3878420481-1+2*2^9*c.k,105039893806022+c.lower,105040277021703+c.upper)) = pointBounds29560 := by
 decide +kernel
def cuts29561 : List PrefixCut := [⟨56,185565689,185565796⟩,
⟨128,430055399,430055638⟩]
theorem checked29561 : checkPrefixCuts (2^48) 3878551553 9 Manual.Count131072.C029561.packed 128 cuts29561 = true := by
 decide +kernel
def pointBounds29561 : List (Nat × Nat × Nat) := [(3878608896,105040508135322,105040891351352)]
theorem point_links_checked29561 : (cuts29561.take 1).map (fun c => (3878551553-1+2*2^9*c.k,105040322569633+c.lower,105040705785556+c.upper)) = pointBounds29561 := by
 decide +kernel
def cuts29562 : List PrefixCut := [⟨47,159507246,159507336⟩,
⟨128,433233901,433234144⟩]
theorem checked29562 : checkPrefixCuts (2^48) 3878682625 9 Manual.Count131072.C029562.packed 128 cuts29562 = true := by
 decide +kernel
def pointBounds29562 : List (Nat × Nat × Nat) := [(3878730752,105040912132278,105041295348530)]
theorem point_links_checked29562 : (cuts29562.take 1).map (fun c => (3878682625-1+2*2^9*c.k,105040752625032+c.lower,105041135841194+c.upper)) = pointBounds29562 := by
 decide +kernel
def cuts29563 : List PrefixCut := [⟨38,129822187,129822256⟩,
⟨128,434235188,434235427⟩]
theorem checked29563 : checkPrefixCuts (2^48) 3878813697 9 Manual.Count131072.C029563.packed 128 cuts29563 = true := by
 decide +kernel
def pointBounds29563 : List (Nat × Nat × Nat) := [(3878852608,105041315681120,105041698897594)]
theorem point_links_checked29563 : (cuts29563.take 1).map (fun c => (3878813697-1+2*2^9*c.k,105041185858933+c.lower,105041569075338+c.upper)) = pointBounds29563 := by
 decide +kernel
def cuts29564 : List PrefixCut := [⟨29,94479027,94479081⟩,
⟨128,430302024,430302264⟩]
theorem checked29564 : checkPrefixCuts (2^48) 3878944769 9 Manual.Count131072.C029564.packed 128 cuts29564 = true := by
 decide +kernel
def pointBounds29564 : List (Nat × Nat × Nat) := [(3878974464,105041714573148,105042097789846)]
theorem point_links_checked29564 : (cuts29564.take 1).map (fun c => (3878944769-1+2*2^9*c.k,105041620094121+c.lower,105042003310765+c.upper)) = pointBounds29564 := by
 decide +kernel
def cuts29565 : List PrefixCut := [⟨20,67845628,67845665⟩,
⟨128,428328354,428328594⟩]
theorem checked29565 : checkPrefixCuts (2^48) 3879075841 9 Manual.Count131072.C029565.packed 128 cuts29565 = true := by
 decide +kernel
def pointBounds29565 : List (Nat × Nat × Nat) := [(3879096320,105042118241773,105042501458694)]
theorem point_links_checked29565 : (cuts29565.take 1).map (fun c => (3879075841-1+2*2^9*c.k,105042050396145+c.lower,105042433613029+c.upper)) = pointBounds29565 := by
 decide +kernel
def cuts29566 : List PrefixCut := [⟨11,37513415,37513436⟩,
⟨128,431143716,431143956⟩]
theorem checked29566 : checkPrefixCuts (2^48) 3879206913 9 Manual.Count131072.C029566.packed 128 cuts29566 = true := by
 decide +kernel
def pointBounds29566 : List (Nat × Nat × Nat) := [(3879218176,105042516237914,105042899455059)]
theorem point_links_checked29566 : (cuts29566.take 1).map (fun c => (3879206913-1+2*2^9*c.k,105042478724499+c.lower,105042861941623+c.upper)) = pointBounds29566 := by
 decide +kernel
def cuts29567 : List PrefixCut := [⟨2,7618532,7618535⟩,
⟨121,410523593,410523821⟩,
⟨128,434031437,434031678⟩]
theorem checked29567 : checkPrefixCuts (2^48) 3879337985 9 Manual.Count131072.C029567.packed 128 cuts29567 = true := by
 decide +kernel
def pointBounds29567 : List (Nat × Nat × Nat) := [(3879340032,105042917486747,105043300704114),(3879461888,105043320391808,105043703609400)]
theorem point_links_checked29567 : (cuts29567.take 2).map (fun c => (3879337985-1+2*2^9*c.k,105042909868215+c.lower,105043293085579+c.upper)) = pointBounds29567 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000298
