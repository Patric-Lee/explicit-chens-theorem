import PlattAssemblyKernel
import PlattCertificates.Count131072.C070544
import PlattCertificates.Count131072.C070545
import PlattCertificates.Count131072.C070546
import PlattCertificates.Count131072.C070547
import PlattCertificates.Count131072.C070548
import PlattCertificates.Count131072.C070549
import PlattCertificates.Count131072.C070550
import PlattCertificates.Count131072.C070551
import PlattCertificates.Count131072.C070552
import PlattCertificates.Count131072.C070553
import PlattCertificates.Count131072.C070554
import PlattCertificates.Count131072.C070555
import PlattCertificates.Count131072.C070556
import PlattCertificates.Count131072.C070557
import PlattCertificates.Count131072.C070558
import PlattCertificates.Count131072.C070559
import PlattCertificates.Count131072.C070560
import PlattCertificates.Count131072.C070561
import PlattCertificates.Count131072.C070562
import PlattCertificates.Count131072.C070563
import PlattCertificates.Count131072.C070564
import PlattCertificates.Count131072.C070565
import PlattCertificates.Count131072.C070566
import PlattCertificates.Count131072.C070567
import PlattCertificates.Count131072.C070568
import PlattCertificates.Count131072.C070569
import PlattCertificates.Count131072.C070570
import PlattCertificates.Count131072.C070571
import PlattCertificates.Count131072.C070572
import PlattCertificates.Count131072.C070573
import PlattCertificates.Count131072.C070574
import PlattCertificates.Count131072.C070575
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000017
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70544 : List PrefixCut := [⟨15,40470252,40470276⟩,
⟨64,175359998,175360100⟩]
theorem checked70544 : checkPrefixCuts (2^48) 9250275329 10 Manual.Count131072.C070544.packed 64 cuts70544 = true := by
 decide +kernel
def pointBounds70544 : List (Nat × Nat × Nat) := [(9250306048,115908705176910,115909094737983)]
theorem point_links_checked70544 : (cuts70544.take 1).map (fun c => (9250275329-1+2*2^10*c.k,115908664706658+c.lower,115909054267707+c.upper)) = pointBounds70544 := by
 decide +kernel
def cuts70545 : List PrefixCut := [⟨64,174931527,174931627⟩]
theorem checked70545 : checkPrefixCuts (2^48) 9250406401 10 Manual.Count131072.C070545.packed 64 cuts70545 = true := by
 decide +kernel
def cuts70546 : List PrefixCut := [⟨29,78260438,78260481⟩,
⟨64,173742364,173742462⟩]
theorem checked70546 : checkPrefixCuts (2^48) 9250537473 10 Manual.Count131072.C070546.packed 64 cuts70546 = true := by
 decide +kernel
def pointBounds70546 : List (Nat × Nat × Nat) := [(9250596864,115909093258621,115909482819915)]
theorem point_links_checked70546 : (cuts70546.take 1).map (fun c => (9250537473-1+2*2^10*c.k,115909014998183+c.lower,115909404559434+c.upper)) = pointBounds70546 := by
 decide +kernel
def cuts70547 : List PrefixCut := [⟨64,176052389,176052494⟩]
theorem checked70547 : checkPrefixCuts (2^48) 9250668545 10 Manual.Count131072.C070547.packed 64 cuts70547 = true := by
 decide +kernel
def cuts70548 : List PrefixCut := [⟨43,114739999,114740069⟩,
⟨64,172337789,172337897⟩]
theorem checked70548 : checkPrefixCuts (2^48) 9250799617 10 Manual.Count131072.C070548.packed 64 cuts70548 = true := by
 decide +kernel
def pointBounds70548 : List (Nat × Nat × Nat) := [(9250887680,115909479532935,115909869094459)]
theorem point_links_checked70548 : (cuts70548.take 1).map (fun c => (9250799617-1+2*2^10*c.k,115909364792936+c.lower,115909754354390+c.upper)) = pointBounds70548 := by
 decide +kernel
def cuts70549 : List PrefixCut := [⟨64,173278591,173278699⟩]
theorem checked70549 : checkPrefixCuts (2^48) 9250930689 10 Manual.Count131072.C070549.packed 64 cuts70549 = true := by
 decide +kernel
def cuts70550 : List PrefixCut := [⟨57,153742746,153742833⟩,
⟨64,172454622,172454722⟩]
theorem checked70550 : checkPrefixCuts (2^48) 9251061761 10 Manual.Count131072.C070550.packed 64 cuts70550 = true := by
 decide +kernel
def pointBounds70550 : List (Nat × Nat × Nat) := [(9251178496,115909864152062,115910253713819)]
theorem point_links_checked70550 : (cuts70550.take 1).map (fun c => (9251061761-1+2*2^10*c.k,115909710409316+c.lower,115910099970986+c.upper)) = pointBounds70550 := by
 decide +kernel
def cuts70551 : List PrefixCut := [⟨64,173395375,173395482⟩]
theorem checked70551 : checkPrefixCuts (2^48) 9251192833 10 Manual.Count131072.C070551.packed 64 cuts70551 = true := by
 decide +kernel
def cuts70552 : List PrefixCut := [⟨64,176830965,176831063⟩]
theorem checked70552 : checkPrefixCuts (2^48) 9251323905 10 Manual.Count131072.C070552.packed 64 cuts70552 = true := by
 decide +kernel
def cuts70553 : List PrefixCut := [⟨7,19471944,19471951⟩,
⟨64,173207918,173208009⟩]
theorem checked70553 : checkPrefixCuts (2^48) 9251454977 10 Manual.Count131072.C070553.packed 64 cuts70553 = true := by
 decide +kernel
def pointBounds70553 : List (Nat × Nat × Nat) := [(9251469312,115910252562222,115910642124204)]
theorem point_links_checked70553 : (cuts70553.take 1).map (fun c => (9251454977-1+2*2^10*c.k,115910233090278+c.lower,115910622652253+c.upper)) = pointBounds70553 := by
 decide +kernel
def cuts70554 : List PrefixCut := [⟨64,175396011,175396109⟩]
theorem checked70554 : checkPrefixCuts (2^48) 9251586049 10 Manual.Count131072.C070554.packed 64 cuts70554 = true := by
 decide +kernel
def cuts70555 : List PrefixCut := [⟨21,55037017,55037048⟩,
⟨64,172503250,172503350⟩]
theorem checked70555 : checkPrefixCuts (2^48) 9251717121 10 Manual.Count131072.C070555.packed 64 cuts70555 = true := by
 decide +kernel
def pointBounds70555 : List (Nat × Nat × Nat) := [(9251760128,115910636731224,115911026293419)]
theorem point_links_checked70555 : (cuts70555.take 1).map (fun c => (9251717121-1+2*2^10*c.k,115910581694207+c.lower,115910971256371+c.upper)) = pointBounds70555 := by
 decide +kernel
def cuts70556 : List PrefixCut := [⟨64,171040489,171040594⟩]
theorem checked70556 : checkPrefixCuts (2^48) 9251848193 10 Manual.Count131072.C070556.packed 64 cuts70556 = true := by
 decide +kernel
def cuts70557 : List PrefixCut := [⟨35,95619773,95619833⟩,
⟨64,176392506,176392617⟩]
theorem checked70557 : checkPrefixCuts (2^48) 9251979265 10 Manual.Count131072.C070557.packed 64 cuts70557 = true := by
 decide +kernel
def pointBounds70557 : List (Nat × Nat × Nat) := [(9252050944,115911020857719,115911410420148)]
theorem point_links_checked70557 : (cuts70557.take 1).map (fun c => (9251979265-1+2*2^10*c.k,115910925237946+c.lower,115911314800315+c.upper)) = pointBounds70557 := by
 decide +kernel
def cuts70558 : List PrefixCut := [⟨64,172222123,172222225⟩]
theorem checked70558 : checkPrefixCuts (2^48) 9252110337 10 Manual.Count131072.C070558.packed 64 cuts70558 = true := by
 decide +kernel
def cuts70559 : List PrefixCut := [⟨49,136565166,136565247⟩,
⟨64,177543556,177543660⟩]
theorem checked70559 : checkPrefixCuts (2^48) 9252241409 10 Manual.Count131072.C070559.packed 64 cuts70559 = true := by
 decide +kernel
def pointBounds70559 : List (Nat × Nat × Nat) := [(9252341760,115911410417741,115911799980404)]
theorem point_links_checked70559 : (cuts70559.take 1).map (fun c => (9252241409-1+2*2^10*c.k,115911273852575+c.lower,115911663415157+c.upper)) = pointBounds70559 := by
 decide +kernel
def cuts70560 : List PrefixCut := [⟨64,172703977,172704083⟩]
theorem checked70560 : checkPrefixCuts (2^48) 9252372481 10 Manual.Count131072.C070560.packed 64 cuts70560 = true := by
 decide +kernel
def cuts70561 : List PrefixCut := [⟨63,170572066,170572168⟩,
⟨64,173614172,173614275⟩]
theorem checked70561 : checkPrefixCuts (2^48) 9252503553 10 Manual.Count131072.C070561.packed 64 cuts70561 = true := by
 decide +kernel
def pointBounds70561 : List (Nat × Nat × Nat) := [(9252632576,115911794672174,115912184235068)]
theorem point_links_checked70561 : (cuts70561.take 1).map (fun c => (9252503553-1+2*2^10*c.k,115911624100108+c.lower,115912013662900+c.upper)) = pointBounds70561 := by
 decide +kernel
def cuts70562 : List PrefixCut := [⟨64,172425321,172425421⟩]
theorem checked70562 : checkPrefixCuts (2^48) 9252634625 10 Manual.Count131072.C070562.packed 64 cuts70562 = true := by
 decide +kernel
def cuts70563 : List PrefixCut := [⟨64,173700521,173700633⟩]
theorem checked70563 : checkPrefixCuts (2^48) 9252765697 10 Manual.Count131072.C070563.packed 64 cuts70563 = true := by
 decide +kernel
def cuts70564 : List PrefixCut := [⟨13,36230397,36230417⟩,
⟨64,174975707,174975805⟩]
theorem checked70564 : checkPrefixCuts (2^48) 9252896769 10 Manual.Count131072.C070564.packed 64 cuts70564 = true := by
 decide +kernel
def pointBounds70564 : List (Nat × Nat × Nat) := [(9252923392,115912180070519,115912569633646)]
theorem point_links_checked70564 : (cuts70564.take 1).map (fun c => (9252896769-1+2*2^10*c.k,115912143840122+c.lower,115912533403229+c.upper)) = pointBounds70564 := by
 decide +kernel
def cuts70565 : List PrefixCut := [⟨64,174821131,174821237⟩]
theorem checked70565 : checkPrefixCuts (2^48) 9253027841 10 Manual.Count131072.C070565.packed 64 cuts70565 = true := by
 decide +kernel
def cuts70566 : List PrefixCut := [⟨27,73340783,73340828⟩,
⟨64,172902252,172902356⟩]
theorem checked70566 : checkPrefixCuts (2^48) 9253158913 10 Manual.Count131072.C070566.packed 64 cuts70566 = true := by
 decide +kernel
def pointBounds70566 : List (Nat × Nat × Nat) := [(9253214208,115912566977743,115912956541099)]
theorem point_links_checked70566 : (cuts70566.take 1).map (fun c => (9253158913-1+2*2^10*c.k,115912493636960+c.lower,115912883200271+c.upper)) = pointBounds70566 := by
 decide +kernel
def cuts70567 : List PrefixCut := [⟨64,172565186,172565296⟩]
theorem checked70567 : checkPrefixCuts (2^48) 9253289985 10 Manual.Count131072.C070567.packed 64 cuts70567 = true := by
 decide +kernel
def cuts70568 : List PrefixCut := [⟨41,110266447,110266509⟩,
⟨64,171558951,171559047⟩]
theorem checked70568 : checkPrefixCuts (2^48) 9253421057 10 Manual.Count131072.C070568.packed 64 cuts70568 = true := by
 decide +kernel
def pointBounds70568 : List (Nat × Nat × Nat) := [(9253505024,115912949370845,115913338934432)]
theorem point_links_checked70568 : (cuts70568.take 1).map (fun c => (9253421057-1+2*2^10*c.k,115912839104398+c.lower,115913228667923+c.upper)) = pointBounds70568 := by
 decide +kernel
def cuts70569 : List PrefixCut := [⟨64,175419595,175419694⟩]
theorem checked70569 : checkPrefixCuts (2^48) 9253552129 10 Manual.Count131072.C070569.packed 64 cuts70569 = true := by
 decide +kernel
def cuts70570 : List PrefixCut := [⟨55,150779154,150779247⟩,
⟨64,175934185,175934292⟩]
theorem checked70570 : checkPrefixCuts (2^48) 9253683201 10 Manual.Count131072.C070570.packed 64 cuts70570 = true := by
 decide +kernel
def pointBounds70570 : List (Nat × Nat × Nat) := [(9253795840,115913336862098,115913726425911)]
theorem point_links_checked70570 : (cuts70570.take 1).map (fun c => (9253683201-1+2*2^10*c.k,115913186082944+c.lower,115913575646664+c.upper)) = pointBounds70570 := by
 decide +kernel
def cuts70571 : List PrefixCut := [⟨64,175353776,175353876⟩]
theorem checked70571 : checkPrefixCuts (2^48) 9253814273 10 Manual.Count131072.C070571.packed 64 cuts70571 = true := by
 decide +kernel
def cuts70572 : List PrefixCut := [⟨64,175990037,175990141⟩]
theorem checked70572 : checkPrefixCuts (2^48) 9253945345 10 Manual.Count131072.C070572.packed 64 cuts70572 = true := by
 decide +kernel
def cuts70573 : List PrefixCut := [⟨5,13991496,13991505⟩,
⟨64,176048370,176048474⟩]
theorem checked70573 : checkPrefixCuts (2^48) 9254076417 10 Manual.Count131072.C070573.packed 64 cuts70573 = true := by
 decide +kernel
def pointBounds70573 : List (Nat × Nat × Nat) := [(9254086656,115913727352438,115914116916478)]
theorem point_links_checked70573 : (cuts70573.take 1).map (fun c => (9254076417-1+2*2^10*c.k,115913713360942+c.lower,115914102924973+c.upper)) = pointBounds70573 := by
 decide +kernel
def cuts70574 : List PrefixCut := [⟨64,171970171,171970269⟩]
theorem checked70574 : checkPrefixCuts (2^48) 9254207489 10 Manual.Count131072.C070574.packed 64 cuts70574 = true := by
 decide +kernel
def cuts70575 : List PrefixCut := [⟨19,51310764,51310790⟩,
⟨64,174492215,174492316⟩]
theorem checked70575 : checkPrefixCuts (2^48) 9254338561 10 Manual.Count131072.C070575.packed 64 cuts70575 = true := by
 decide +kernel
def pointBounds70575 : List (Nat × Nat × Nat) := [(9254377472,115914112690247,115914502254506)]
theorem point_links_checked70575 : (cuts70575.take 1).map (fun c => (9254338561-1+2*2^10*c.k,115914061379483+c.lower,115914450943716+c.upper)) = pointBounds70575 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000017
