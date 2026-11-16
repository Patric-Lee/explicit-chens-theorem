import PlattAssemblyKernel
import PlattCertificates.Count131072.C028576
import PlattCertificates.Count131072.C028577
import PlattCertificates.Count131072.C028578
import PlattCertificates.Count131072.C028579
import PlattCertificates.Count131072.C028580
import PlattCertificates.Count131072.C028581
import PlattCertificates.Count131072.C028582
import PlattCertificates.Count131072.C028583
import PlattCertificates.Count131072.C028584
import PlattCertificates.Count131072.C028585
import PlattCertificates.Count131072.C028586
import PlattCertificates.Count131072.C028587
import PlattCertificates.Count131072.C028588
import PlattCertificates.Count131072.C028589
import PlattCertificates.Count131072.C028590
import PlattCertificates.Count131072.C028591
import PlattCertificates.Count131072.C028592
import PlattCertificates.Count131072.C028593
import PlattCertificates.Count131072.C028594
import PlattCertificates.Count131072.C028595
import PlattCertificates.Count131072.C028596
import PlattCertificates.Count131072.C028597
import PlattCertificates.Count131072.C028598
import PlattCertificates.Count131072.C028599
import PlattCertificates.Count131072.C028600
import PlattCertificates.Count131072.C028601
import PlattCertificates.Count131072.C028602
import PlattCertificates.Count131072.C028603
import PlattCertificates.Count131072.C028604
import PlattCertificates.Count131072.C028605
import PlattCertificates.Count131072.C028606
import PlattCertificates.Count131072.C028607
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000268
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28576 : List PrefixCut := [⟨24,82127482,82127530⟩,
⟨128,451244287,451244541⟩]
theorem checked28576 : checkPrefixCuts (2^48) 3749445633 9 Manual.Count131072.C028576.packed 128 cuts28576 = true := by
 decide +kernel
def pointBounds28576 : List (Nat × Nat × Nat) := [(3749470208,104608530500146,104608913474167)]
theorem point_links_checked28576 : (cuts28576.take 1).map (fun c => (3749445633-1+2*2^9*c.k,104608448372664+c.lower,104608831346637+c.upper)) = pointBounds28576 := by
 decide +kernel
def cuts28577 : List PrefixCut := [⟨11,37834439,37834462⟩,
⟨126,436365307,436365556⟩,
⟨128,442896035,442896288⟩]
theorem checked28577 : checkPrefixCuts (2^48) 3749576705 9 Manual.Count131072.C028577.packed 128 cuts28577 = true := by
 decide +kernel
def pointBounds28577 : List (Nat × Nat × Nat) := [(3749587968,104608937451390,104609320425640),(3749705728,104609335982258,104609718956734)]
theorem point_links_checked28577 : (cuts28577.take 2).map (fun c => (3749576705-1+2*2^9*c.k,104608899616951+c.lower,104609282591178+c.upper)) = pointBounds28577 := by
 decide +kernel
def cuts28578 : List PrefixCut := [⟨113,393789247,393789469⟩,
⟨128,446108405,446108656⟩]
theorem checked28578 : checkPrefixCuts (2^48) 3749707777 9 Manual.Count131072.C028578.packed 128 cuts28578 = true := by
 decide +kernel
def pointBounds28578 : List (Nat × Nat × Nat) := [(3749823488,104609736302233,104610119276935)]
theorem point_links_checked28578 : (cuts28578.take 1).map (fun c => (3749707777-1+2*2^9*c.k,104609342512986+c.lower,104609725487466+c.upper)) = pointBounds28578 := by
 decide +kernel
def cuts28579 : List PrefixCut := [⟨100,347612966,347613157⟩,
⟨128,441664227,441664474⟩]
theorem checked28579 : checkPrefixCuts (2^48) 3749838849 9 Manual.Count131072.C028579.packed 128 cuts28579 = true := by
 decide +kernel
def pointBounds28579 : List (Nat × Nat × Nat) := [(3749941248,104610136234357,104610519209279)]
theorem point_links_checked28579 : (cuts28579.take 1).map (fun c => (3749838849-1+2*2^9*c.k,104609788621391+c.lower,104610171596122+c.upper)) = pointBounds28579 := by
 decide +kernel
def cuts28580 : List PrefixCut := [⟨87,305793130,305793297⟩,
⟨128,453282830,453283078⟩]
theorem checked28580 : checkPrefixCuts (2^48) 3749969921 9 Manual.Count131072.C028580.packed 128 cuts28580 = true := by
 decide +kernel
def pointBounds28580 : List (Nat × Nat × Nat) := [(3750059008,104610536078748,104610919053893)]
theorem point_links_checked28580 : (cuts28580.take 1).map (fun c => (3749969921-1+2*2^9*c.k,104610230285618+c.lower,104610613260596+c.upper)) = pointBounds28580 := by
 decide +kernel
def cuts28581 : List PrefixCut := [⟨74,253167880,253168025⟩,
⟨128,446436759,446437008⟩]
theorem checked28581 : checkPrefixCuts (2^48) 3750100993 9 Manual.Count131072.C028581.packed 128 cuts28581 = true := by
 decide +kernel
def pointBounds28581 : List (Nat × Nat × Nat) := [(3750176768,104610936736328,104611319711699)]
theorem point_links_checked28581 : (cuts28581.take 1).map (fun c => (3750100993-1+2*2^9*c.k,104610683568448+c.lower,104611066543674+c.upper)) = pointBounds28581 := by
 decide +kernel
def cuts28582 : List PrefixCut := [⟨61,206325385,206325499⟩,
⟨128,441167432,441167677⟩]
theorem checked28582 : checkPrefixCuts (2^48) 3750232065 9 Manual.Count131072.C028582.packed 128 cuts28582 = true := by
 decide +kernel
def pointBounds28582 : List (Nat × Nat × Nat) := [(3750294528,104611336330592,104611719306181)]
theorem point_links_checked28582 : (cuts28582.take 1).map (fun c => (3750232065-1+2*2^9*c.k,104611130005207+c.lower,104611512980682+c.upper)) = pointBounds28582 := by
 decide +kernel
def cuts28583 : List PrefixCut := [⟨48,166465820,166465911⟩,
⟨128,442127821,442128068⟩]
theorem checked28583 : checkPrefixCuts (2^48) 3750363137 9 Manual.Count131072.C028583.packed 128 cuts28583 = true := by
 decide +kernel
def pointBounds28583 : List (Nat × Nat × Nat) := [(3750412288,104611737638459,104612120614270)]
theorem point_links_checked28583 : (cuts28583.take 1).map (fun c => (3750363137-1+2*2^9*c.k,104611571172639+c.lower,104611954148359+c.upper)) = pointBounds28583 := by
 decide +kernel
def cuts28584 : List PrefixCut := [⟨35,124057201,124057271⟩,
⟨128,449617204,449617454⟩]
theorem checked28584 : checkPrefixCuts (2^48) 3750494209 9 Manual.Count131072.C028584.packed 128 cuts28584 = true := by
 decide +kernel
def pointBounds28584 : List (Nat × Nat × Nat) := [(3750530048,104612137357661,104612520333698)]
theorem point_links_checked28584 : (cuts28584.take 1).map (fun c => (3750494209-1+2*2^9*c.k,104612013300460+c.lower,104612396276427+c.upper)) = pointBounds28584 := by
 decide +kernel
def cuts28585 : List PrefixCut := [⟨22,75647611,75647653⟩,
⟨128,444498327,444498578⟩]
theorem checked28585 : checkPrefixCuts (2^48) 3750625281 9 Manual.Count131072.C028585.packed 128 cuts28585 = true := by
 decide +kernel
def pointBounds28585 : List (Nat × Nat × Nat) := [(3750647808,104612538565275,104612921541534)]
theorem point_links_checked28585 : (cuts28585.take 1).map (fun c => (3750625281-1+2*2^9*c.k,104612462917664+c.lower,104612845893881+c.upper)) = pointBounds28585 := by
 decide +kernel
def cuts28586 : List PrefixCut := [⟨9,30243030,30243048⟩,
⟨124,426322496,426322735⟩,
⟨128,440580526,440580771⟩]
theorem checked28586 : checkPrefixCuts (2^48) 3750756353 9 Manual.Count131072.C028586.packed 128 cuts28586 = true := by
 decide +kernel
def pointBounds28586 : List (Nat × Nat × Nat) := [(3750765568,104612937659021,104613320635507),(3750883328,104613333738487,104613716715194)]
theorem point_links_checked28586 : (cuts28586.take 2).map (fun c => (3750756353-1+2*2^9*c.k,104612907415991+c.lower,104613290392459+c.upper)) = pointBounds28586 := by
 decide +kernel
def cuts28587 : List PrefixCut := [⟨111,386986760,386986980⟩,
⟨128,442516188,442516441⟩]
theorem checked28587 : checkPrefixCuts (2^48) 3750887425 9 Manual.Count131072.C028587.packed 128 cuts28587 = true := by
 decide +kernel
def pointBounds28587 : List (Nat × Nat × Nat) := [(3751001088,104613734983277,104614117960210)]
theorem point_links_checked28587 : (cuts28587.take 1).map (fun c => (3750887425-1+2*2^9*c.k,104613347996517+c.lower,104613730973230+c.upper)) = pointBounds28587 := by
 decide +kernel
def cuts28588 : List PrefixCut := [⟨98,340375055,340375242⟩,
⟨128,445577315,445577562⟩]
theorem checked28588 : checkPrefixCuts (2^48) 3751018497 9 Manual.Count131072.C028588.packed 128 cuts28588 = true := by
 decide +kernel
def pointBounds28588 : List (Nat × Nat × Nat) := [(3751118848,104614130887760,104614513864913)]
theorem point_links_checked28588 : (cuts28588.take 1).map (fun c => (3751018497-1+2*2^9*c.k,104613790512705+c.lower,104614173489671+c.upper)) = pointBounds28588 := by
 decide +kernel
def cuts28589 : List PrefixCut := [⟨85,296917830,296917996⟩,
⟨128,447737754,447738008⟩]
theorem checked28589 : checkPrefixCuts (2^48) 3751149569 9 Manual.Count131072.C028589.packed 128 cuts28589 = true := by
 decide +kernel
def pointBounds28589 : List (Nat × Nat × Nat) := [(3751236608,104614533007850,104614915985229)]
theorem point_links_checked28589 : (cuts28589.take 1).map (fun c => (3751149569-1+2*2^9*c.k,104614236090020+c.lower,104614619067233+c.upper)) = pointBounds28589 := by
 decide +kernel
def cuts28590 : List PrefixCut := [⟨72,249786904,249787045⟩,
⟨128,443370229,443370478⟩]
theorem checked28590 : checkPrefixCuts (2^48) 3751280641 9 Manual.Count131072.C028590.packed 128 cuts28590 = true := by
 decide +kernel
def pointBounds28590 : List (Nat × Nat × Nat) := [(3751354368,104614933614678,104615316592286)]
theorem point_links_checked28590 : (cuts28590.take 1).map (fun c => (3751280641-1+2*2^9*c.k,104614683827774+c.lower,104615066805241+c.upper)) = pointBounds28590 := by
 decide +kernel
def cuts28591 : List PrefixCut := [⟨59,204985044,204985163⟩,
⟨128,447706465,447706715⟩]
theorem checked28591 : checkPrefixCuts (2^48) 3751411713 9 Manual.Count131072.C028591.packed 128 cuts28591 = true := by
 decide +kernel
def pointBounds28591 : List (Nat × Nat × Nat) := [(3751472128,104615332183047,104615715160882)]
theorem point_links_checked28591 : (cuts28591.take 1).map (fun c => (3751411713-1+2*2^9*c.k,104615127198003+c.lower,104615510175719+c.upper)) = pointBounds28591 := by
 decide +kernel
def cuts28592 : List PrefixCut := [⟨46,160261150,160261243⟩,
⟨128,447540736,447540990⟩]
theorem checked28592 : checkPrefixCuts (2^48) 3751542785 9 Manual.Count131072.C028592.packed 128 cuts28592 = true := by
 decide +kernel
def pointBounds28592 : List (Nat × Nat × Nat) := [(3751589888,104615735165618,104616118143677)]
theorem point_links_checked28592 : (cuts28592.take 1).map (fun c => (3751542785-1+2*2^9*c.k,104615574904468+c.lower,104615957882434+c.upper)) = pointBounds28592 := by
 decide +kernel
def cuts28593 : List PrefixCut := [⟨33,115240157,115240223⟩,
⟨128,448125354,448125604⟩]
theorem checked28593 : checkPrefixCuts (2^48) 3751673857 9 Manual.Count131072.C028593.packed 128 cuts28593 = true := by
 decide +kernel
def pointBounds28593 : List (Nat × Nat × Nat) := [(3751707648,104616137685361,104616520663647)]
theorem point_links_checked28593 : (cuts28593.take 1).map (fun c => (3751673857-1+2*2^9*c.k,104616022445204+c.lower,104616405423424+c.upper)) = pointBounds28593 := by
 decide +kernel
def cuts28594 : List PrefixCut := [⟨20,71647590,71647628⟩,
⟨128,445709036,445709281⟩]
theorem checked28594 : checkPrefixCuts (2^48) 3751804929 9 Manual.Count131072.C028594.packed 128 cuts28594 = true := by
 decide +kernel
def pointBounds28594 : List (Nat × Nat × Nat) := [(3751825408,104616542218148,104616925196656)]
theorem point_links_checked28594 : (cuts28594.take 1).map (fun c => (3751804929-1+2*2^9*c.k,104616470570558+c.lower,104616853549028+c.upper)) = pointBounds28594 := by
 decide +kernel
def cuts28595 : List PrefixCut := [⟨7,23031498,23031511⟩,
⟨122,421987369,421987609⟩,
⟨128,443442713,443442964⟩]
theorem checked28595 : checkPrefixCuts (2^48) 3751936001 9 Manual.Count131072.C028595.packed 128 cuts28595 = true := by
 decide +kernel
def pointBounds28595 : List (Nat × Nat × Nat) := [(3751943168,104616939311092,104617322289820),(3752060928,104617338266963,104617721245918)]
theorem point_links_checked28595 : (cuts28595.take 2).map (fun c => (3751936001-1+2*2^9*c.k,104616916279594+c.lower,104617299258309+c.upper)) = pointBounds28595 := by
 decide +kernel
def cuts28596 : List PrefixCut := [⟨109,383639520,383639734⟩,
⟨128,451529180,451529429⟩]
theorem checked28596 : checkPrefixCuts (2^48) 3752067073 9 Manual.Count131072.C028596.packed 128 cuts28596 = true := by
 decide +kernel
def pointBounds28596 : List (Nat × Nat × Nat) := [(3752178688,104617743361827,104618126341007)]
theorem point_links_checked28596 : (cuts28596.take 1).map (fun c => (3752067073-1+2*2^9*c.k,104617359722307+c.lower,104617742701273+c.upper)) = pointBounds28596 := by
 decide +kernel
def cuts28597 : List PrefixCut := [⟨96,335092067,335092256⟩,
⟨128,447012520,447012771⟩]
theorem checked28597 : checkPrefixCuts (2^48) 3752198145 9 Manual.Count131072.C028597.packed 128 cuts28597 = true := by
 decide +kernel
def pointBounds28597 : List (Nat × Nat × Nat) := [(3752296448,104618146343554,104618529322958)]
theorem point_links_checked28597 : (cuts28597.take 1).map (fun c => (3752198145-1+2*2^9*c.k,104617811251487+c.lower,104618194230702+c.upper)) = pointBounds28597 := by
 decide +kernel
def cuts28598 : List PrefixCut := [⟨83,292773908,292774066⟩,
⟨128,446771941,446772181⟩]
theorem checked28598 : checkPrefixCuts (2^48) 3752329217 9 Manual.Count131072.C028598.packed 128 cuts28598 = true := by
 decide +kernel
def pointBounds28598 : List (Nat × Nat × Nat) := [(3752414208,104618551037915,104618934017539)]
theorem point_links_checked28598 : (cuts28598.take 1).map (fun c => (3752329217-1+2*2^9*c.k,104618258264007+c.lower,104618641243473+c.upper)) = pointBounds28598 := by
 decide +kernel
def cuts28599 : List PrefixCut := [⟨70,244232709,244232846⟩,
⟨128,445256100,445256349⟩]
theorem checked28599 : checkPrefixCuts (2^48) 3752460289 9 Manual.Count131072.C028599.packed 128 cuts28599 = true := by
 decide +kernel
def pointBounds28599 : List (Nat × Nat × Nat) := [(3752531968,104618949268657,104619332248500)]
theorem point_links_checked28599 : (cuts28599.take 1).map (fun c => (3752460289-1+2*2^9*c.k,104618705035948+c.lower,104619088015654+c.upper)) = pointBounds28599 := by
 decide +kernel
def cuts28600 : List PrefixCut := [⟨57,197569904,197570017⟩,
⟨128,447415704,447415954⟩]
theorem checked28600 : checkPrefixCuts (2^48) 3752591361 9 Manual.Count131072.C028600.packed 128 cuts28600 = true := by
 decide +kernel
def pointBounds28600 : List (Nat × Nat × Nat) := [(3752649728,104619347861952,104619730842020)]
theorem point_links_checked28600 : (cuts28600.take 1).map (fun c => (3752591361-1+2*2^9*c.k,104619150292048+c.lower,104619533272003+c.upper)) = pointBounds28600 := by
 decide +kernel
def cuts28601 : List PrefixCut := [⟨44,154960460,154960545⟩,
⟨128,445524991,445525241⟩]
theorem checked28601 : checkPrefixCuts (2^48) 3752722433 9 Manual.Count131072.C028601.packed 128 cuts28601 = true := by
 decide +kernel
def pointBounds28601 : List (Nat × Nat × Nat) := [(3752767488,104619752668212,104620135648502)]
theorem point_links_checked28601 : (cuts28601.take 1).map (fun c => (3752722433-1+2*2^9*c.k,104619597707752+c.lower,104619980687957+c.upper)) = pointBounds28601 := by
 decide +kernel
def cuts28602 : List PrefixCut := [⟨31,107328695,107328755⟩,
⟨128,449034518,449034765⟩]
theorem checked28602 : checkPrefixCuts (2^48) 3752853505 9 Manual.Count131072.C028602.packed 128 cuts28602 = true := by
 decide +kernel
def pointBounds28602 : List (Nat × Nat × Nat) := [(3752885248,104620150561438,104620533541953)]
theorem point_links_checked28602 : (cuts28602.take 1).map (fun c => (3752853505-1+2*2^9*c.k,104620043232743+c.lower,104620426213198+c.upper)) = pointBounds28602 := by
 decide +kernel
def cuts28603 : List PrefixCut := [⟨18,63075076,63075112⟩,
⟨128,445943884,445944132⟩]
theorem checked28603 : checkPrefixCuts (2^48) 3752984577 9 Manual.Count131072.C028603.packed 128 cuts28603 = true := by
 decide +kernel
def pointBounds28603 : List (Nat × Nat × Nat) := [(3753003008,104620555342337,104620938323075)]
theorem point_links_checked28603 : (cuts28603.take 1).map (fun c => (3752984577-1+2*2^9*c.k,104620492267261+c.lower,104620875247963+c.upper)) = pointBounds28603 := by
 decide +kernel
def cuts28604 : List PrefixCut := [⟨5,18074425,18074435⟩,
⟨120,422079959,422080192⟩,
⟨128,448328252,448328501⟩]
theorem checked28604 : checkPrefixCuts (2^48) 3753115649 9 Manual.Count131072.C028604.packed 128 cuts28604 = true := by
 decide +kernel
def pointBounds28604 : List (Nat × Nat × Nat) := [(3753120768,104620956285570,104621339266530),(3753238528,104621360291104,104621743272287)]
theorem point_links_checked28604 : (cuts28604.take 2).map (fun c => (3753115649-1+2*2^9*c.k,104620938211145+c.lower,104621321192095+c.upper)) = pointBounds28604 := by
 decide +kernel
def cuts28605 : List PrefixCut := [⟨107,370020144,370020353⟩,
⟨128,445462741,445462992⟩]
theorem checked28605 : checkPrefixCuts (2^48) 3753246721 9 Manual.Count131072.C028605.packed 128 cuts28605 = true := by
 decide +kernel
def pointBounds28605 : List (Nat × Nat × Nat) := [(3753356288,104621756559541,104622139540949)]
theorem point_links_checked28605 : (cuts28605.take 1).map (fun c => (3753246721-1+2*2^9*c.k,104621386539397+c.lower,104621769520596+c.upper)) = pointBounds28605 := by
 decide +kernel
def cuts28606 : List PrefixCut := [⟨94,326662805,326662987⟩,
⟨128,443047522,443047768⟩]
theorem checked28606 : checkPrefixCuts (2^48) 3753377793 9 Manual.Count131072.C028606.packed 128 cuts28606 = true := by
 decide +kernel
def pointBounds28606 : List (Nat × Nat × Nat) := [(3753474048,104622158664943,104622541646575)]
theorem point_links_checked28606 : (cuts28606.take 1).map (fun c => (3753377793-1+2*2^9*c.k,104621832002138+c.lower,104622214983588+c.upper)) = pointBounds28606 := by
 decide +kernel
def cuts28607 : List PrefixCut := [⟨81,281433650,281433810⟩,
⟨128,445356677,445356928⟩]
theorem checked28607 : checkPrefixCuts (2^48) 3753508865 9 Manual.Count131072.C028607.packed 128 cuts28607 = true := by
 decide +kernel
def pointBounds28607 : List (Nat × Nat × Nat) := [(3753591808,104622556483310,104622939465166)]
theorem point_links_checked28607 : (cuts28607.take 1).map (fun c => (3753508865-1+2*2^9*c.k,104622275049660+c.lower,104622658031356+c.upper)) = pointBounds28607 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000268
