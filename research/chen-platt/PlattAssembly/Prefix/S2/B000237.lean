import PlattAssemblyKernel
import PlattCertificates.Count131072.C017584
import PlattCertificates.Count131072.C017585
import PlattCertificates.Count131072.C017586
import PlattCertificates.Count131072.C017587
import PlattCertificates.Count131072.C017588
import PlattCertificates.Count131072.C017589
import PlattCertificates.Count131072.C017590
import PlattCertificates.Count131072.C017591
import PlattCertificates.Count131072.C017592
import PlattCertificates.Count131072.C017593
import PlattCertificates.Count131072.C017594
import PlattCertificates.Count131072.C017595
import PlattCertificates.Count131072.C017596
import PlattCertificates.Count131072.C017597
import PlattCertificates.Count131072.C017598
import PlattCertificates.Count131072.C017599
import PlattCertificates.Count131072.C017600
import PlattCertificates.Count131072.C017601
import PlattCertificates.Count131072.C017602
import PlattCertificates.Count131072.C017603
import PlattCertificates.Count131072.C017604
import PlattCertificates.Count131072.C017605
import PlattCertificates.Count131072.C017606
import PlattCertificates.Count131072.C017607
import PlattCertificates.Count131072.C017608
import PlattCertificates.Count131072.C017609
import PlattCertificates.Count131072.C017610
import PlattCertificates.Count131072.C017611
import PlattCertificates.Count131072.C017612
import PlattCertificates.Count131072.C017613
import PlattCertificates.Count131072.C017614
import PlattCertificates.Count131072.C017615
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000237
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17584 : List PrefixCut := [⟨49,288945128,288945306⟩,
⟨120,705892866,705893301⟩,
⟨128,752463400,752463863⟩]
theorem checked17584 : checkPrefixCuts (2^48) 2308702209 9 Manual.Count131072.C017584.packed 128 cuts17584 = true := by
 decide +kernel
def pointBounds17584 : List (Nat × Nat × Nat) := [(2308752384,98348007100660,98348386464636),(2308825088,98348424048398,98348803412631)]
theorem point_links_checked17584 : (cuts17584.take 2).map (fun c => (2308702209-1+2*2^9*c.k,98347718155532+c.lower,98348097519330+c.upper)) = pointBounds17584 := by
 decide +kernel
def cuts17585 : List PrefixCut := [⟨63,360001581,360001802⟩,
⟨128,735597094,735597548⟩]
theorem checked17585 : checkPrefixCuts (2^48) 2308833281 9 Manual.Count131072.C017585.packed 128 cuts17585 = true := by
 decide +kernel
def pointBounds17585 : List (Nat × Nat × Nat) := [(2308897792,98348830620513,98349209984995)]
theorem point_links_checked17585 : (cuts17585.take 1).map (fun c => (2308833281-1+2*2^9*c.k,98348470618932+c.lower,98348849983193+c.upper)) = pointBounds17585 := by
 decide +kernel
def cuts17586 : List PrefixCut := [⟨6,37181053,37181076⟩,
⟨77,445800018,445800298⟩,
⟨128,748233168,748233640⟩]
theorem checked17586 : checkPrefixCuts (2^48) 2308964353 9 Manual.Count131072.C017586.packed 128 cuts17586 = true := by
 decide +kernel
def pointBounds17586 : List (Nat × Nat × Nat) := [(2308970496,98349243397079,98349622761817),(2309043200,98349652016044,98350031381039)]
theorem point_links_checked17586 : (cuts17586.take 2).map (fun c => (2308964353-1+2*2^9*c.k,98349206216026+c.lower,98349585580741+c.upper)) = pointBounds17586 := by
 decide +kernel
def cuts17587 : List PrefixCut := [⟨20,116534296,116534365⟩,
⟨91,526955859,526956181⟩,
⟨128,739048660,739049113⟩]
theorem checked17587 : checkPrefixCuts (2^48) 2309095425 9 Manual.Count131072.C017587.packed 128 cuts17587 = true := by
 decide +kernel
def pointBounds17587 : List (Nat × Nat × Nat) := [(2309115904,98350070983490,98350450348746),(2309188608,98350481405053,98350860770562)]
theorem point_links_checked17587 : (cuts17587.take 2).map (fun c => (2309095425-1+2*2^9*c.k,98349954449194+c.lower,98350333814381+c.upper)) = pointBounds17587 := by
 decide +kernel
def cuts17588 : List PrefixCut := [⟨34,199778487,199778606⟩,
⟨105,615903033,615903410⟩,
⟨128,750586083,750586543⟩]
theorem checked17588 : checkPrefixCuts (2^48) 2309226497 9 Manual.Count131072.C017588.packed 128 cuts17588 = true := by
 decide +kernel
def pointBounds17588 : List (Nat × Nat × Nat) := [(2309261312,98350893276341,98351272642100),(2309334016,98351309400887,98351688766904)]
theorem point_links_checked17588 : (cuts17588.take 2).map (fun c => (2309226497-1+2*2^9*c.k,98350693497854+c.lower,98351072863494+c.upper)) = pointBounds17588 := by
 decide +kernel
def cuts17589 : List PrefixCut := [⟨48,275334148,275334320⟩,
⟨119,682169596,682170020⟩,
⟨128,734942697,734943152⟩]
theorem checked17589 : checkPrefixCuts (2^48) 2309357569 9 Manual.Count131072.C017589.packed 128 cuts17589 = true := by
 decide +kernel
def pointBounds17589 : List (Nat × Nat × Nat) := [(2309406720,98351719418085,98352098784357),(2309479424,98352126253533,98352505620057)]
theorem point_links_checked17589 : (cuts17589.take 2).map (fun c => (2309357569-1+2*2^9*c.k,98351444083937+c.lower,98351823450037+c.upper)) = pointBounds17589 := by
 decide +kernel
def cuts17590 : List PrefixCut := [⟨62,356365123,356365344⟩,
⟨128,736119624,736120078⟩]
theorem checked17590 : checkPrefixCuts (2^48) 2309488641 9 Manual.Count131072.C017590.packed 128 cuts17590 = true := by
 decide +kernel
def pointBounds17590 : List (Nat × Nat × Nat) := [(2309552128,98352535391757,98352914758533)]
theorem point_links_checked17590 : (cuts17590.take 1).map (fun c => (2309488641-1+2*2^9*c.k,98352179026634+c.lower,98352558393189+c.upper)) = pointBounds17590 := by
 decide +kernel
def cuts17591 : List PrefixCut := [⟨5,29248928,29248944⟩,
⟨76,438605067,438605337⟩,
⟨128,745461524,745461979⟩]
theorem checked17591 : checkPrefixCuts (2^48) 2309619713 9 Manual.Count131072.C017591.packed 128 cuts17591 = true := by
 decide +kernel
def pointBounds17591 : List (Nat × Nat × Nat) := [(2309624832,98352944395186,98353323762211),(2309697536,98353353751325,98353733118604)]
theorem point_links_checked17591 : (cuts17591.take 2).map (fun c => (2309619713-1+2*2^9*c.k,98352915146258+c.lower,98353294513267+c.upper)) = pointBounds17591 := by
 decide +kernel
def cuts17592 : List PrefixCut := [⟨19,109798785,109798853⟩,
⟨90,514864074,514864395⟩,
⟨128,733233341,733233792⟩]
theorem checked17592 : checkPrefixCuts (2^48) 2309750785 9 Manual.Count131072.C017592.packed 128 cuts17592 = true := by
 decide +kernel
def pointBounds17592 : List (Nat × Nat × Nat) := [(2309770240,98353770406567,98354149774099),(2309842944,98354175471856,98354554839641)]
theorem point_links_checked17592 : (cuts17592.take 2).map (fun c => (2309750785-1+2*2^9*c.k,98353660607782+c.lower,98354039975246+c.upper)) = pointBounds17592 := by
 decide +kernel
def cuts17593 : List PrefixCut := [⟨33,188267408,188267526⟩,
⟨104,596962880,596963250⟩,
⟨128,733801064,733801518⟩]
theorem checked17593 : checkPrefixCuts (2^48) 2309881857 9 Manual.Count131072.C017593.packed 128 cuts17593 = true := by
 decide +kernel
def pointBounds17593 : List (Nat × Nat × Nat) := [(2309915648,98354582108531,98354961476564),(2309988352,98354990804003,98355370172288)]
theorem point_links_checked17593 : (cuts17593.take 2).map (fun c => (2309881857-1+2*2^9*c.k,98354393841123+c.lower,98354773209038+c.upper)) = pointBounds17593 := by
 decide +kernel
def cuts17594 : List PrefixCut := [⟨47,270260321,270260496⟩,
⟨118,682097987,682098414⟩,
⟨128,738145888,738146351⟩]
theorem checked17594 : checkPrefixCuts (2^48) 2310012929 9 Manual.Count131072.C017594.packed 128 cuts17594 = true := by
 decide +kernel
def pointBounds17594 : List (Nat × Nat × Nat) := [(2310061056,98355397902508,98355777271052),(2310133760,98355809740174,98356189108970)]
theorem point_links_checked17594 : (cuts17594.take 2).map (fun c => (2310012929-1+2*2^9*c.k,98355127642187+c.lower,98355507010556+c.upper)) = pointBounds17594 := by
 decide +kernel
def cuts17595 : List PrefixCut := [⟨61,348344462,348344676⟩,
⟨128,745901517,745901970⟩]
theorem checked17595 : checkPrefixCuts (2^48) 2310144001 9 Manual.Count131072.C017595.packed 128 cuts17595 = true := by
 decide +kernel
def pointBounds17595 : List (Nat × Nat × Nat) := [(2310206464,98356214132537,98356593501583)]
theorem point_links_checked17595 : (cuts17595.take 1).map (fun c => (2310144001-1+2*2^9*c.k,98355865788075+c.lower,98356245156907+c.upper)) = pointBounds17595 := by
 decide +kernel
def cuts17596 : List PrefixCut := [⟨4,22539657,22539671⟩,
⟨75,431292530,431292793⟩,
⟨128,743544368,743544820⟩]
theorem checked17596 : checkPrefixCuts (2^48) 2310275073 9 Manual.Count131072.C017596.packed 128 cuts17596 = true := by
 decide +kernel
def pointBounds17596 : List (Nat × Nat × Nat) := [(2310279168,98356634229249,98357013598548),(2310351872,98357042982122,98357422351670)]
theorem point_links_checked17596 : (cuts17596.take 2).map (fun c => (2310275073-1+2*2^9*c.k,98356611689592+c.lower,98356991058877+c.upper)) = pointBounds17596 := by
 decide +kernel
def cuts17597 : List PrefixCut := [⟨18,104650856,104650916⟩,
⟨89,509967028,509967334⟩,
⟨128,736680265,736680705⟩]
theorem checked17597 : checkPrefixCuts (2^48) 2310406145 9 Manual.Count131072.C017597.packed 128 cuts17597 = true := by
 decide +kernel
def pointBounds17597 : List (Nat × Nat × Nat) := [(2310424576,98357459884816,98357839254613),(2310497280,98357865200988,98358244571031)]
theorem point_links_checked17597 : (cuts17597.take 2).map (fun c => (2310406145-1+2*2^9*c.k,98357355233960+c.lower,98357734603697+c.upper)) = pointBounds17597 := by
 decide +kernel
def cuts17598 : List PrefixCut := [⟨32,178955655,178955763⟩,
⟨103,595209915,595210280⟩,
⟨128,738100132,738100582⟩]
theorem checked17598 : checkPrefixCuts (2^48) 2310537217 9 Manual.Count131072.C017598.packed 128 cuts17598 = true := by
 decide +kernel
def pointBounds17598 : List (Nat × Nat × Nat) := [(2310569984,98358270869880,98358650240165),(2310642688,98358687124140,98359066494682)]
theorem point_links_checked17598 : (cuts17598.take 2).map (fun c => (2310537217-1+2*2^9*c.k,98358091914225+c.lower,98358471284402+c.upper)) = pointBounds17598 := by
 decide +kernel
def cuts17599 : List PrefixCut := [⟨46,266041990,266042158⟩,
⟨117,681417453,681417879⟩,
⟨128,744879809,744880275⟩]
theorem checked17599 : checkPrefixCuts (2^48) 2310668289 9 Manual.Count131072.C017599.packed 128 cuts17599 = true := by
 decide +kernel
def pointBounds17599 : List (Nat × Nat × Nat) := [(2310715392,98359096056347,98359475427142),(2310788096,98359511431810,98359890802863)]
theorem point_links_checked17599 : (cuts17599.take 2).map (fun c => (2310668289-1+2*2^9*c.k,98358830014357+c.lower,98359209384984+c.upper)) = pointBounds17599 := by
 decide +kernel
def cuts17600 : List PrefixCut := [⟨60,357990298,357990516⟩,
⟨128,749709957,749710411⟩]
theorem checked17600 : checkPrefixCuts (2^48) 2310799361 9 Manual.Count131072.C017600.packed 128 cuts17600 = true := by
 decide +kernel
def pointBounds17600 : List (Nat × Nat × Nat) := [(2310860800,98359932884464,98360312255775)]
theorem point_links_checked17600 : (cuts17600.take 1).map (fun c => (2310799361-1+2*2^9*c.k,98359574894166+c.lower,98359954265259+c.upper)) = pointBounds17600 := by
 decide +kernel
def cuts17601 : List PrefixCut := [⟨3,17904815,17904826⟩,
⟨74,437503980,437504247⟩,
⟨128,744795534,744795985⟩]
theorem checked17601 : checkPrefixCuts (2^48) 2310930433 9 Manual.Count131072.C017601.packed 128 cuts17601 = true := by
 decide +kernel
def pointBounds17601 : List (Nat × Nat × Nat) := [(2310933504,98360342508938,98360721880496),(2311006208,98360762108103,98361141479917)]
theorem point_links_checked17601 : (cuts17601.take 2).map (fun c => (2310930433-1+2*2^9*c.k,98360324604123+c.lower,98360703975670+c.upper)) = pointBounds17601 := by
 decide +kernel
def cuts17602 : List PrefixCut := [⟨17,98044326,98044381⟩,
⟨88,510066015,510066319⟩,
⟨128,746823463,746823912⟩]
theorem checked17602 : checkPrefixCuts (2^48) 2311061505 9 Manual.Count131072.C017602.packed 128 cuts17602 = true := by
 decide +kernel
def pointBounds17602 : List (Nat × Nat × Nat) := [(2311078912,98361167443983,98361546816036),(2311151616,98361579465672,98361958837974)]
theorem point_links_checked17602 : (cuts17602.take 2).map (fun c => (2311061505-1+2*2^9*c.k,98361069399657+c.lower,98361448771655+c.upper)) = pointBounds17602 := by
 decide +kernel
def cuts17603 : List PrefixCut := [⟨31,188404315,188404428⟩,
⟨102,606732849,606733218⟩,
⟨128,755671651,755672110⟩]
theorem checked17603 : checkPrefixCuts (2^48) 2311192577 9 Manual.Count131072.C017603.packed 128 cuts17603 = true := by
 decide +kernel
def pointBounds17603 : List (Nat × Nat × Nat) := [(2311224320,98362004627435,98362383999995),(2311297024,98362422955969,98362802328785)]
theorem point_links_checked17603 : (cuts17603.take 2).map (fun c => (2311192577-1+2*2^9*c.k,98361816223120+c.lower,98362195595567+c.upper)) = pointBounds17603 := by
 decide +kernel
def cuts17604 : List PrefixCut := [⟨45,263287532,263287697⟩,
⟨116,678058227,678058648⟩,
⟨128,748565513,748565977⟩]
theorem checked17604 : checkPrefixCuts (2^48) 2311323649 9 Manual.Count131072.C017604.packed 128 cuts17604 = true := by
 decide +kernel
def pointBounds17604 : List (Nat × Nat × Nat) := [(2311369728,98362835182303,98363214555374),(2311442432,98363249952998,98363629326325)]
theorem point_links_checked17604 : (cuts17604.take 2).map (fun c => (2311323649-1+2*2^9*c.k,98362571894771+c.lower,98362951267677+c.upper)) = pointBounds17604 := by
 decide +kernel
def cuts17605 : List PrefixCut := [⟨59,341814891,341815102⟩,
⟨128,742312767,742313224⟩]
theorem checked17605 : checkPrefixCuts (2^48) 2311454721 9 Manual.Count131072.C017605.packed 128 cuts17605 = true := by
 decide +kernel
def pointBounds17605 : List (Nat × Nat × Nat) := [(2311515136,98363662275175,98364041648756)]
theorem point_links_checked17605 : (cuts17605.take 1).map (fun c => (2311454721-1+2*2^9*c.k,98363320460284+c.lower,98363699833654+c.upper)) = pointBounds17605 := by
 decide +kernel
def cuts17606 : List PrefixCut := [⟨2,11811395,11811402⟩,
⟨73,423864077,423864338⟩,
⟨128,731433832,731434285⟩]
theorem checked17606 : checkPrefixCuts (2^48) 2311585793 9 Manual.Count131072.C017606.packed 128 cuts17606 = true := by
 decide +kernel
def pointBounds17606 : List (Nat × Nat × Nat) := [(2311587840,98364074584446,98364453958280),(2311660544,98364486637128,98364866011216)]
theorem point_links_checked17606 : (cuts17606.take 2).map (fun c => (2311585793-1+2*2^9*c.k,98364062773051+c.lower,98364442146878+c.upper)) = pointBounds17606 := by
 decide +kernel
def cuts17607 : List PrefixCut := [⟨16,91563271,91563328⟩,
⟨87,507364597,507364909⟩,
⟨128,744541988,744542446⟩]
theorem checked17607 : checkPrefixCuts (2^48) 2311716865 9 Manual.Count131072.C017607.packed 128 cuts17607 = true := by
 decide +kernel
def pointBounds17607 : List (Nat × Nat × Nat) := [(2311733248,98364885770154,98365265144491),(2311805952,98365301571480,98365680946072)]
theorem point_links_checked17607 : (cuts17607.take 2).map (fun c => (2311716865-1+2*2^9*c.k,98364794206883+c.lower,98365173581163+c.upper)) = pointBounds17607 := by
 decide +kernel
def cuts17608 : List PrefixCut := [⟨30,173375419,173375529⟩,
⟨101,582941357,582941723⟩,
⟨128,740360254,740360717⟩]
theorem checked17608 : checkPrefixCuts (2^48) 2311847937 9 Manual.Count131072.C017608.packed 128 cuts17608 = true := by
 decide +kernel
def pointBounds17608 : List (Nat × Nat × Nat) := [(2311878656,98365712124290,98366091499138),(2311951360,98366121690228,98366501065332)]
theorem point_links_checked17608 : (cuts17608.take 2).map (fun c => (2311847937-1+2*2^9*c.k,98365538748871+c.lower,98365918123609+c.upper)) = pointBounds17608 := by
 decide +kernel
def cuts17609 : List PrefixCut := [⟨44,247264351,247264503⟩,
⟨115,650960875,650961274⟩,
⟨128,728630840,728631282⟩]
theorem checked17609 : checkPrefixCuts (2^48) 2311979009 9 Manual.Count131072.C017609.packed 128 cuts17609 = true := by
 decide +kernel
def pointBounds17609 : List (Nat × Nat × Nat) := [(2312024064,98366526373476,98366905748829),(2312096768,98366930070000,98367309445600)]
theorem point_links_checked17609 : (cuts17609.take 2).map (fun c => (2311979009-1+2*2^9*c.k,98366279109125+c.lower,98366658484326+c.upper)) = pointBounds17609 := by
 decide +kernel
def cuts17610 : List PrefixCut := [⟨58,335874648,335874864⟩,
⟨128,739424088,739424555⟩]
theorem checked17610 : checkPrefixCuts (2^48) 2312110081 9 Manual.Count131072.C017610.packed 128 cuts17610 = true := by
 decide +kernel
def pointBounds17610 : List (Nat × Nat × Nat) := [(2312169472,98367343614613,98367722990472)]
theorem point_links_checked17610 : (cuts17610.take 1).map (fun c => (2312110081-1+2*2^9*c.k,98367007739965+c.lower,98367387115608+c.upper)) = pointBounds17610 := by
 decide +kernel
def cuts17611 : List PrefixCut := [⟨1,5843159,5843162⟩,
⟨72,416440236,416440496⟩,
⟨128,737556307,737556774⟩]
theorem checked17611 : checkPrefixCuts (2^48) 2312241153 9 Manual.Count131072.C017611.packed 128 cuts17611 = true := by
 decide +kernel
def pointBounds17611 : List (Nat × Nat × Nat) := [(2312242176,98367753007212,98368132383325),(2312314880,98368163604289,98368542980659)]
theorem point_links_checked17611 : (cuts17611.take 2).map (fun c => (2312241153-1+2*2^9*c.k,98367747164053+c.lower,98368126540163+c.upper)) = pointBounds17611 := by
 decide +kernel
def cuts17612 : List PrefixCut := [⟨15,85085910,85085963⟩,
⟨86,489814514,489814822⟩,
⟨128,735932041,735932496⟩]
theorem checked17612 : checkPrefixCuts (2^48) 2312372225 9 Manual.Count131072.C017612.packed 128 cuts17612 = true := by
 decide +kernel
def pointBounds17612 : List (Nat × Nat × Nat) := [(2312387584,98368569806270,98368949182900),(2312460288,98368974534874,98369353911759)]
theorem point_links_checked17612 : (cuts17612.take 2).map (fun c => (2312372225-1+2*2^9*c.k,98368484720360+c.lower,98368864096937+c.upper)) = pointBounds17612 := by
 decide +kernel
def cuts17613 : List PrefixCut := [⟨29,170283358,170283460⟩,
⟨100,576081895,576082252⟩,
⟨128,738811599,738812056⟩]
theorem checked17613 : checkPrefixCuts (2^48) 2312503297 9 Manual.Count131072.C017613.packed 128 cuts17613 = true := by
 decide +kernel
def pointBounds17613 : List (Nat × Nat × Nat) := [(2312532992,98369390935759,98369770312893),(2312605696,98369796734296,98370176111685)]
theorem point_links_checked17613 : (cuts17613.take 2).map (fun c => (2312503297-1+2*2^9*c.k,98369220652401+c.lower,98369600029433+c.upper)) = pointBounds17613 := by
 decide +kernel
def cuts17614 : List PrefixCut := [⟨43,245003521,245003673⟩,
⟨114,660634902,660635308⟩,
⟨128,740838675,740839130⟩]
theorem checked17614 : checkPrefixCuts (2^48) 2312634369 9 Manual.Count131072.C017614.packed 128 cuts17614 = true := by
 decide +kernel
def pointBounds17614 : List (Nat × Nat × Nat) := [(2312678400,98370204467521,98370583845162),(2312751104,98370620098902,98370999476797)]
theorem point_links_checked17614 : (cuts17614.take 2).map (fun c => (2312634369-1+2*2^9*c.k,98369959464000+c.lower,98370338841489+c.upper)) = pointBounds17614 := by
 decide +kernel
def cuts17615 : List PrefixCut := [⟨57,328599075,328599274⟩,
⟨128,738241096,738241552⟩]
theorem checked17615 : checkPrefixCuts (2^48) 2312765441 9 Manual.Count131072.C017615.packed 128 cuts17615 = true := by
 decide +kernel
def pointBounds17615 : List (Nat × Nat × Nat) := [(2312823808,98371028901750,98371408279893),(2312896512,98371438543771,98371817922171)]
theorem point_links_checked17615 : (cuts17615.take 2).map (fun c => (2312765441-1+2*2^9*c.k,98370700302675+c.lower,98371079680619+c.upper)) = pointBounds17615 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000237
