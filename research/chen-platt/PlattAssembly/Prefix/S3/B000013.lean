import PlattAssemblyKernel
import PlattCertificates.Count131072.C020416
import PlattCertificates.Count131072.C020417
import PlattCertificates.Count131072.C020418
import PlattCertificates.Count131072.C020419
import PlattCertificates.Count131072.C020420
import PlattCertificates.Count131072.C020421
import PlattCertificates.Count131072.C020422
import PlattCertificates.Count131072.C020423
import PlattCertificates.Count131072.C020424
import PlattCertificates.Count131072.C020425
import PlattCertificates.Count131072.C020426
import PlattCertificates.Count131072.C020427
import PlattCertificates.Count131072.C020428
import PlattCertificates.Count131072.C020429
import PlattCertificates.Count131072.C020430
import PlattCertificates.Count131072.C020431
import PlattCertificates.Count131072.C020432
import PlattCertificates.Count131072.C020433
import PlattCertificates.Count131072.C020434
import PlattCertificates.Count131072.C020435
import PlattCertificates.Count131072.C020436
import PlattCertificates.Count131072.C020437
import PlattCertificates.Count131072.C020438
import PlattCertificates.Count131072.C020439
import PlattCertificates.Count131072.C020440
import PlattCertificates.Count131072.C020441
import PlattCertificates.Count131072.C020442
import PlattCertificates.Count131072.C020443
import PlattCertificates.Count131072.C020444
import PlattCertificates.Count131072.C020445
import PlattCertificates.Count131072.C020446
import PlattCertificates.Count131072.C020447
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000013
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20416 : List PrefixCut := [⟨44,215418697,215418821⟩,
⟨126,617152769,617153123⟩,
⟨128,628600695,628601055⟩]
theorem checked20416 : checkPrefixCuts (2^48) 2679898113 9 Manual.Count131072.C020416.packed 128 cuts20416 = true := by
 decide +kernel
def pointBounds20416 : List (Nat × Nat × Nat) := [(2679943168,100287695421493,100288075947589),(2680027136,100288097155565,100288477681891)]
theorem point_links_checked20416 : (cuts20416.take 2).map (fun c => (2679898113-1+2*2^9*c.k,100287480002796+c.lower,100287860528768+c.upper)) = pointBounds20416 := by
 decide +kernel
def cuts20417 : List PrefixCut := [⟨80,394684729,394684960⟩,
⟨128,638757326,638757696⟩]
theorem checked20417 : checkPrefixCuts (2^48) 2680029185 9 Manual.Count131072.C020417.packed 128 cuts20417 = true := by
 decide +kernel
def pointBounds20417 : List (Nat × Nat × Nat) := [(2680111104,100288503288220,100288883814783)]
theorem point_links_checked20417 : (cuts20417.take 1).map (fun c => (2680029185-1+2*2^9*c.k,100288108603491+c.lower,100288489129823+c.upper)) = pointBounds20417 := by
 decide +kernel
def cuts20418 : List PrefixCut := [⟨34,172969547,172969647⟩,
⟨116,584957766,584958106⟩,
⟨128,645132375,645132751⟩]
theorem checked20418 : checkPrefixCuts (2^48) 2680160257 9 Manual.Count131072.C020418.packed 128 cuts20418 = true := by
 decide +kernel
def pointBounds20418 : List (Nat × Nat × Nat) := [(2680195072,100288920330364,100289300857166),(2680279040,100289332318583,100289712845625)]
theorem point_links_checked20418 : (cuts20418.take 2).map (fun c => (2680160257-1+2*2^9*c.k,100288747360817+c.lower,100289127887519+c.upper)) = pointBounds20418 := by
 decide +kernel
def cuts20419 : List PrefixCut := [⟨70,349805404,349805606⟩,
⟨128,637749864,637750237⟩]
theorem checked20419 : checkPrefixCuts (2^48) 2680291329 9 Manual.Count131072.C020419.packed 128 cuts20419 = true := by
 decide +kernel
def pointBounds20419 : List (Nat × Nat × Nat) := [(2680363008,100289742298596,100290122825876)]
theorem point_links_checked20419 : (cuts20419.take 1).map (fun c => (2680291329-1+2*2^9*c.k,100289392493192+c.lower,100289773020270+c.upper)) = pointBounds20419 := by
 decide +kernel
def cuts20420 : List PrefixCut := [⟨24,116037066,116037137⟩,
⟨106,522526114,522526418⟩,
⟨128,629527950,629528318⟩]
theorem checked20420 : checkPrefixCuts (2^48) 2680422401 9 Manual.Count131072.C020420.packed 128 cuts20420 = true := by
 decide +kernel
def pointBounds20420 : List (Nat × Nat × Nat) := [(2680446976,100290146280122,100290526807644),(2680530944,100290552769170,100290933296925)]
theorem point_links_checked20420 : (cuts20420.take 2).map (fun c => (2680422401-1+2*2^9*c.k,100290030243056+c.lower,100290410770507+c.upper)) = pointBounds20420 := by
 decide +kernel
def cuts20421 : List PrefixCut := [⟨60,296639319,296639491⟩,
⟨128,631282235,631282604⟩]
theorem checked20421 : checkPrefixCuts (2^48) 2680553473 9 Manual.Count131072.C020421.packed 128 cuts20421 = true := by
 decide +kernel
def pointBounds20421 : List (Nat × Nat × Nat) := [(2680614912,100290956410325,100291336938316)]
theorem point_links_checked20421 : (cuts20421.take 1).map (fun c => (2680553473-1+2*2^9*c.k,100290659771006+c.lower,100291040298825+c.upper)) = pointBounds20421 := by
 decide +kernel
def cuts20422 : List PrefixCut := [⟨14,68985552,68985591⟩,
⟨96,477956320,477956595⟩,
⟨128,641436084,641436453⟩]
theorem checked20422 : checkPrefixCuts (2^48) 2680684545 9 Manual.Count131072.C020422.packed 128 cuts20422 = true := by
 decide +kernel
def pointBounds20422 : List (Nat × Nat × Nat) := [(2680698880,100291360038793,100291740567020),(2680782848,100291769009561,100292149538024)]
theorem point_links_checked20422 : (cuts20422.take 2).map (fun c => (2680684545-1+2*2^9*c.k,100291291053241+c.lower,100291671581429+c.upper)) = pointBounds20422 := by
 decide +kernel
def cuts20423 : List PrefixCut := [⟨50,247893179,247893323⟩,
⟨128,634580292,634580660⟩]
theorem checked20423 : checkPrefixCuts (2^48) 2680815617 9 Manual.Count131072.C020423.packed 128 cuts20423 = true := by
 decide +kernel
def pointBounds20423 : List (Nat × Nat × Nat) := [(2680866816,100292180382504,100292560911205)]
theorem point_links_checked20423 : (cuts20423.take 1).map (fun c => (2680815617-1+2*2^9*c.k,100291932489325+c.lower,100292313017882+c.upper)) = pointBounds20423 := by
 decide +kernel
def cuts20424 : List PrefixCut := [⟨4,21943074,21943085⟩,
⟨86,428565656,428565907⟩,
⟨128,634024370,634024740⟩]
theorem checked20424 : checkPrefixCuts (2^48) 2680946689 9 Manual.Count131072.C020424.packed 128 cuts20424 = true := by
 decide +kernel
def pointBounds20424 : List (Nat × Nat × Nat) := [(2680950784,100292589012691,100292969541627),(2681034752,100292995635273,100293376164449)]
theorem point_links_checked20424 : (cuts20424.take 2).map (fun c => (2680946689-1+2*2^9*c.k,100292567069617+c.lower,100292947598542+c.upper)) = pointBounds20424 := by
 decide +kernel
def cuts20425 : List PrefixCut := [⟨40,200416236,200416351⟩,
⟨122,602709047,602709403⟩,
⟨128,631263802,631264175⟩]
theorem checked20425 : checkPrefixCuts (2^48) 2681077761 9 Manual.Count131072.C020425.packed 128 cuts20425 = true := by
 decide +kernel
def pointBounds20425 : List (Nat × Nat × Nat) := [(2681118720,100293401510223,100293782039633),(2681202688,100293803803034,100294184332685)]
theorem point_links_checked20425 : (cuts20425.take 2).map (fun c => (2681077761-1+2*2^9*c.k,100293201093987+c.lower,100293581623282+c.upper)) = pointBounds20425 := by
 decide +kernel
def cuts20426 : List PrefixCut := [⟨76,372780687,372780905⟩,
⟨128,625564135,625564503⟩]
theorem checked20426 : checkPrefixCuts (2^48) 2681208833 9 Manual.Count131072.C020426.packed 128 cuts20426 = true := by
 decide +kernel
def pointBounds20426 : List (Nat × Nat × Nat) := [(2681286656,100294205138476,100294585668362)]
theorem point_links_checked20426 : (cuts20426.take 1).map (fun c => (2681208833-1+2*2^9*c.k,100293832357789+c.lower,100294212887457+c.upper)) = pointBounds20426 := by
 decide +kernel
def cuts20427 : List PrefixCut := [⟨30,155152832,155152924⟩,
⟨112,562026718,562027046⟩,
⟨128,638340385,638340756⟩]
theorem checked20427 : checkPrefixCuts (2^48) 2681339905 9 Manual.Count131072.C020427.packed 128 cuts20427 = true := by
 decide +kernel
def pointBounds20427 : List (Nat × Nat × Nat) := [(2681370624,100294613074756,100294993604884),(2681454592,100295019948642,100295400479006)]
theorem point_links_checked20427 : (cuts20427.take 2).map (fun c => (2681339905-1+2*2^9*c.k,100294457921924+c.lower,100294838451960+c.upper)) = pointBounds20427 := by
 decide +kernel
def cuts20428 : List PrefixCut := [⟨66,328972846,328973042⟩,
⟨128,636419534,636419912⟩]
theorem checked20428 : checkPrefixCuts (2^48) 2681470977 9 Manual.Count131072.C020428.packed 128 cuts20428 = true := by
 decide +kernel
def pointBounds20428 : List (Nat × Nat × Nat) := [(2681538560,100295425235155,100295805765758)]
theorem point_links_checked20428 : (cuts20428.take 1).map (fun c => (2681470977-1+2*2^9*c.k,100295096262309+c.lower,100295476792716+c.upper)) = pointBounds20428 := by
 decide +kernel
def cuts20429 : List PrefixCut := [⟨20,98771876,98771932⟩,
⟨102,504033123,504033414⟩,
⟨128,635443793,635444162⟩]
theorem checked20429 : checkPrefixCuts (2^48) 2681602049 9 Manual.Count131072.C020429.packed 128 cuts20429 = true := by
 decide +kernel
def pointBounds20429 : List (Nat × Nat × Nat) := [(2681622528,100295831453719,100296211984560),(2681706496,100296236714966,100296617246042)]
theorem point_links_checked20429 : (cuts20429.take 2).map (fun c => (2681602049-1+2*2^9*c.k,100295732681843+c.lower,100296113212628+c.upper)) = pointBounds20429 := by
 decide +kernel
def cuts20430 : List PrefixCut := [⟨56,274992447,274992612⟩,
⟨128,627960785,627961159⟩]
theorem checked20430 : checkPrefixCuts (2^48) 2681733121 9 Manual.Count131072.C020430.packed 128 cuts20430 = true := by
 decide +kernel
def pointBounds20430 : List (Nat × Nat × Nat) := [(2681790464,100296643118083,100297023649402)]
theorem point_links_checked20430 : (cuts20430.take 1).map (fun c => (2681733121-1+2*2^9*c.k,100296368125636+c.lower,100296748656790+c.upper)) = pointBounds20430 := by
 decide +kernel
def cuts20431 : List PrefixCut := [⟨10,48803953,48803979⟩,
⟨92,451823062,451823318⟩,
⟨128,632337975,632338336⟩]
theorem checked20431 : checkPrefixCuts (2^48) 2681864193 9 Manual.Count131072.C020431.packed 128 cuts20431 = true := by
 decide +kernel
def pointBounds20431 : List (Nat × Nat × Nat) := [(2681874432,100297044890374,100297425421928),(2681958400,100297447909483,100297828441267)]
theorem point_links_checked20431 : (cuts20431.take 2).map (fun c => (2681864193-1+2*2^9*c.k,100296996086421+c.lower,100297376617949+c.upper)) = pointBounds20431 := by
 decide +kernel
def cuts20432 : List PrefixCut := [⟨46,223331224,223331354⟩,
⟨128,636085138,636085510⟩]
theorem checked20432 : checkPrefixCuts (2^48) 2681995265 9 Manual.Count131072.C020432.packed 128 cuts20432 = true := by
 decide +kernel
def pointBounds20432 : List (Nat × Nat × Nat) := [(2682042368,100297851755620,100298232287639),(2682126336,100298264509534,100298645041795)]
theorem point_links_checked20432 : (cuts20432.take 2).map (fun c => (2681995265-1+2*2^9*c.k,100297628424396+c.lower,100298008956285+c.upper)) = pointBounds20432 := by
 decide +kernel
def cuts20433 : List PrefixCut := [⟨82,402246657,402246893⟩,
⟨128,629652665,629653036⟩]
theorem checked20433 : checkPrefixCuts (2^48) 2682126337 9 Manual.Count131072.C020433.packed 128 cuts20433 = true := by
 decide +kernel
def pointBounds20433 : List (Nat × Nat × Nat) := [(2682210304,100298666756191,100299047288688)]
theorem point_links_checked20433 : (cuts20433.take 1).map (fun c => (2682126337-1+2*2^9*c.k,100298264509534+c.lower,100298645041795+c.upper)) = pointBounds20433 := by
 decide +kernel
def cuts20434 : List PrefixCut := [⟨36,177241679,177241783⟩,
⟨118,591006190,591006537⟩,
⟨128,643158701,643159079⟩]
theorem checked20434 : checkPrefixCuts (2^48) 2682257409 9 Manual.Count131072.C020434.packed 128 cuts20434 = true := by
 decide +kernel
def pointBounds20434 : List (Nat × Nat × Nat) := [(2682294272,100299071403878,100299451936614),(2682378240,100299485168389,100299865701368)]
theorem point_links_checked20434 : (cuts20434.take 2).map (fun c => (2682257409-1+2*2^9*c.k,100298894162199+c.lower,100299274694831+c.upper)) = pointBounds20434 := by
 decide +kernel
def cuts20435 : List PrefixCut := [⟨72,355512905,355513109⟩,
⟨128,630745391,630745756⟩]
theorem checked20435 : checkPrefixCuts (2^48) 2682388481 9 Manual.Count131072.C020435.packed 128 cuts20435 = true := by
 decide +kernel
def pointBounds20435 : List (Nat × Nat × Nat) := [(2682462208,100299892833805,100300273367019)]
theorem point_links_checked20435 : (cuts20435.take 1).map (fun c => (2682388481-1+2*2^9*c.k,100299537320900+c.lower,100299917853910+c.upper)) = pointBounds20435 := by
 decide +kernel
def cuts20436 : List PrefixCut := [⟨26,130426476,130426552⟩,
⟨108,527783599,527783908⟩,
⟨128,623894507,623894873⟩]
theorem checked20436 : checkPrefixCuts (2^48) 2682519553 9 Manual.Count131072.C020436.packed 128 cuts20436 = true := by
 decide +kernel
def pointBounds20436 : List (Nat × Nat × Nat) := [(2682546176,100300298492767,100300679026218),(2682630144,100300695849890,100301076383574)]
theorem point_links_checked20436 : (cuts20436.take 2).map (fun c => (2682519553-1+2*2^9*c.k,100300168066291+c.lower,100300548599666+c.upper)) = pointBounds20436 := by
 decide +kernel
def cuts20437 : List PrefixCut := [⟨62,299764818,299764992⟩,
⟨128,623758901,623759268⟩]
theorem checked20437 : checkPrefixCuts (2^48) 2682650625 9 Manual.Count131072.C020437.packed 128 cuts20437 = true := by
 decide +kernel
def pointBounds20437 : List (Nat × Nat × Nat) := [(2682714112,100301091725616,100301472259531)]
theorem point_links_checked20437 : (cuts20437.take 1).map (fun c => (2682650625-1+2*2^9*c.k,100300791960798+c.lower,100301172494539+c.upper)) = pointBounds20437 := by
 decide +kernel
def cuts20438 : List PrefixCut := [⟨16,79843157,79843203⟩,
⟨98,487549763,487550050⟩,
⟨128,634535003,634535375⟩]
theorem checked20438 : checkPrefixCuts (2^48) 2682781697 9 Manual.Count131072.C020438.packed 128 cuts20438 = true := by
 decide +kernel
def pointBounds20438 : List (Nat × Nat × Nat) := [(2682798080,100301495562856,100301876097010),(2682882048,100301903269462,100302283803857)]
theorem point_links_checked20438 : (cuts20438.take 2).map (fun c => (2682781697-1+2*2^9*c.k,100301415719699+c.lower,100301796253807+c.upper)) = pointBounds20438 := by
 decide +kernel
def cuts20439 : List PrefixCut := [⟨52,257456187,257456340⟩,
⟨128,636077562,636077935⟩]
theorem checked20439 : checkPrefixCuts (2^48) 2682912769 9 Manual.Count131072.C020439.packed 128 cuts20439 = true := by
 decide +kernel
def pointBounds20439 : List (Nat × Nat × Nat) := [(2682966016,100302307710889,100302688245522)]
theorem point_links_checked20439 : (cuts20439.take 1).map (fun c => (2682912769-1+2*2^9*c.k,100302050254702+c.lower,100302430789182+c.upper)) = pointBounds20439 := by
 decide +kernel
def cuts20440 : List PrefixCut := [⟨6,29164610,29164627⟩,
⟨88,421726303,421726550⟩,
⟨128,623247790,623248156⟩]
theorem checked20440 : checkPrefixCuts (2^48) 2683043841 9 Manual.Count131072.C020440.packed 128 cuts20440 = true := by
 decide +kernel
def pointBounds20440 : List (Nat × Nat × Nat) := [(2683049984,100302715496874,100303096031744),(2683133952,100303108058567,100303488593667)]
theorem point_links_checked20440 : (cuts20440.take 2).map (fun c => (2683043841-1+2*2^9*c.k,100302686332264+c.lower,100303066867117+c.upper)) = pointBounds20440 := by
 decide +kernel
def cuts20441 : List PrefixCut := [⟨42,209386057,209386180⟩,
⟨124,611259225,611259586⟩,
⟨128,629721383,629721755⟩]
theorem checked20441 : checkPrefixCuts (2^48) 2683174913 9 Manual.Count131072.C020441.packed 128 cuts20441 = true := by
 decide +kernel
def pointBounds20441 : List (Nat × Nat × Nat) := [(2683217920,100303518966111,100303899501453),(2683301888,100303920839279,100304301374859)]
theorem point_links_checked20441 : (cuts20441.take 2).map (fun c => (2683174913-1+2*2^9*c.k,100303309580054+c.lower,100303690115273+c.upper)) = pointBounds20441 := by
 decide +kernel
def cuts20442 : List PrefixCut := [⟨78,389902083,389902303⟩,
⟨128,633362018,633362377⟩]
theorem checked20442 : checkPrefixCuts (2^48) 2683305985 9 Manual.Count131072.C020442.packed 128 cuts20442 = true := by
 decide +kernel
def pointBounds20442 : List (Nat × Nat × Nat) := [(2683385856,100304329203520,100304709739331)]
theorem point_links_checked20442 : (cuts20442.take 1).map (fun c => (2683305985-1+2*2^9*c.k,100303939301437+c.lower,100304319837028+c.upper)) = pointBounds20442 := by
 decide +kernel
def cuts20443 : List PrefixCut := [⟨32,156395148,156395234⟩,
⟨114,563579969,563580293⟩,
⟨128,633750429,633750793⟩]
theorem checked20443 : checkPrefixCuts (2^48) 2683437057 9 Manual.Count131072.C020443.packed 128 cuts20443 = true := by
 decide +kernel
def pointBounds20443 : List (Nat × Nat × Nat) := [(2683469824,100304729058603,100305109594639),(2683553792,100305136243424,100305516779698)]
theorem point_links_checked20443 : (cuts20443.take 2).map (fun c => (2683437057-1+2*2^9*c.k,100304572663455+c.lower,100304953199405+c.upper)) = pointBounds20443 := by
 decide +kernel
def cuts20444 : List PrefixCut := [⟨68,328610773,328610971⟩,
⟨128,625643387,625643757⟩]
theorem checked20444 : checkPrefixCuts (2^48) 2683568129 9 Manual.Count131072.C020444.packed 128 cuts20444 = true := by
 decide +kernel
def pointBounds20444 : List (Nat × Nat × Nat) := [(2683637760,100305535024657,100305915561169)]
theorem point_links_checked20444 : (cuts20444.take 1).map (fun c => (2683568129-1+2*2^9*c.k,100305206413884+c.lower,100305586950198+c.upper)) = pointBounds20444 := by
 decide +kernel
def cuts20445 : List PrefixCut := [⟨22,107819454,107819516⟩,
⟨104,516644202,516644497⟩,
⟨128,637674013,637674378⟩]
theorem checked20445 : checkPrefixCuts (2^48) 2683699201 9 Manual.Count131072.C020445.packed 128 cuts20445 = true := by
 decide +kernel
def pointBounds20445 : List (Nat × Nat × Nat) := [(2683721728,100305939876725,100306320413471),(2683805696,100306348701473,100306729238452)]
theorem point_links_checked20445 : (cuts20445.take 2).map (fun c => (2683699201-1+2*2^9*c.k,100305832057271+c.lower,100306212593955+c.upper)) = pointBounds20445 := by
 decide +kernel
def cuts20446 : List PrefixCut := [⟨58,286733429,286733595⟩,
⟨128,633343121,633343489⟩]
theorem checked20446 : checkPrefixCuts (2^48) 2683830273 9 Manual.Count131072.C020446.packed 128 cuts20446 = true := by
 decide +kernel
def pointBounds20446 : List (Nat × Nat × Nat) := [(2683889664,100306756464713,100307137001928)]
theorem point_links_checked20446 : (cuts20446.take 1).map (fun c => (2683830273-1+2*2^9*c.k,100306469731284+c.lower,100306850268333+c.upper)) = pointBounds20446 := by
 decide +kernel
def cuts20447 : List PrefixCut := [⟨12,60092052,60092088⟩,
⟨94,462376549,462376819⟩,
⟨128,630795348,630795714⟩]
theorem checked20447 : checkPrefixCuts (2^48) 2683961345 9 Manual.Count131072.C020447.packed 128 cuts20447 = true := by
 decide +kernel
def pointBounds20447 : List (Nat × Nat × Nat) := [(2683973632,100307163166457,100307543703910),(2684057600,100307565450954,100307945988641)]
theorem point_links_checked20447 : (cuts20447.take 2).map (fun c => (2683961345-1+2*2^9*c.k,100307103074405+c.lower,100307483611822+c.upper)) = pointBounds20447 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000013
