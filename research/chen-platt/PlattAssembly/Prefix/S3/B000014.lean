import PlattAssemblyKernel
import PlattCertificates.Count131072.C020448
import PlattCertificates.Count131072.C020449
import PlattCertificates.Count131072.C020450
import PlattCertificates.Count131072.C020451
import PlattCertificates.Count131072.C020452
import PlattCertificates.Count131072.C020453
import PlattCertificates.Count131072.C020454
import PlattCertificates.Count131072.C020455
import PlattCertificates.Count131072.C020456
import PlattCertificates.Count131072.C020457
import PlattCertificates.Count131072.C020458
import PlattCertificates.Count131072.C020459
import PlattCertificates.Count131072.C020460
import PlattCertificates.Count131072.C020461
import PlattCertificates.Count131072.C020462
import PlattCertificates.Count131072.C020463
import PlattCertificates.Count131072.C020464
import PlattCertificates.Count131072.C020465
import PlattCertificates.Count131072.C020466
import PlattCertificates.Count131072.C020467
import PlattCertificates.Count131072.C020468
import PlattCertificates.Count131072.C020469
import PlattCertificates.Count131072.C020470
import PlattCertificates.Count131072.C020471
import PlattCertificates.Count131072.C020472
import PlattCertificates.Count131072.C020473
import PlattCertificates.Count131072.C020474
import PlattCertificates.Count131072.C020475
import PlattCertificates.Count131072.C020476
import PlattCertificates.Count131072.C020477
import PlattCertificates.Count131072.C020478
import PlattCertificates.Count131072.C020479
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20448 : List PrefixCut := [⟨48,240669409,240669552⟩,
⟨128,632966667,632967036⟩]
theorem checked20448 : checkPrefixCuts (2^48) 2684092417 9 Manual.Count131072.C020448.packed 128 cuts20448 = true := by
 decide +kernel
def pointBounds20448 : List (Nat × Nat × Nat) := [(2684141568,100307974539162,100308355077088)]
theorem point_links_checked20448 : (cuts20448.take 1).map (fun c => (2684092417-1+2*2^9*c.k,100307733869753+c.lower,100308114407536+c.upper)) = pointBounds20448 := by
 decide +kernel
def cuts20449 : List PrefixCut := [⟨2,10066814,10066820⟩,
⟨84,415039842,415040087⟩,
⟨128,632935728,632936104⟩]
theorem checked20449 : checkPrefixCuts (2^48) 2684223489 9 Manual.Count131072.C020449.packed 128 cuts20449 = true := by
 decide +kernel
def pointBounds20449 : List (Nat × Nat × Nat) := [(2684225536,100308376903234,100308757441392),(2684309504,100308781876262,100309162414659)]
theorem point_links_checked20449 : (cuts20449.take 2).map (fun c => (2684223489-1+2*2^9*c.k,100308366836420+c.lower,100308747374572+c.upper)) = pointBounds20449 := by
 decide +kernel
def cuts20450 : List PrefixCut := [⟨38,191049105,191049218⟩,
⟨120,594528927,594529278⟩,
⟨128,632171014,632171387⟩]
theorem checked20450 : checkPrefixCuts (2^48) 2684354561 9 Manual.Count131072.C020450.packed 128 cuts20450 = true := by
 decide +kernel
def pointBounds20450 : List (Nat × Nat × Nat) := [(2684393472,100309190821253,100309571359894),(2684477440,100309594301075,100309974839954)]
theorem point_links_checked20450 : (cuts20450.take 2).map (fun c => (2684354561-1+2*2^9*c.k,100308999772148+c.lower,100309380310676+c.upper)) = pointBounds20450 := by
 decide +kernel
def cuts20451 : List PrefixCut := [⟨74,367397864,367398080⟩,
⟨128,632874026,632874401⟩]
theorem checked20451 : checkPrefixCuts (2^48) 2684485633 9 Manual.Count131072.C020451.packed 128 cuts20451 = true := by
 decide +kernel
def pointBounds20451 : List (Nat × Nat × Nat) := [(2684561408,100309999341026,100310379880143)]
theorem point_links_checked20451 : (cuts20451.take 1).map (fun c => (2684485633-1+2*2^9*c.k,100309631943162+c.lower,100310012482063+c.upper)) = pointBounds20451 := by
 decide +kernel
def cuts20452 : List PrefixCut := [⟨28,139970460,139970541⟩,
⟨110,540267026,540267343⟩,
⟨128,628544472,628544842⟩]
theorem checked20452 : checkPrefixCuts (2^48) 2684616705 9 Manual.Count131072.C020452.packed 128 cuts20452 = true := by
 decide +kernel
def pointBounds20452 : List (Nat × Nat × Nat) := [(2684645376,100310404787648,100310785327005),(2684729344,100310805084214,100311185623807)]
theorem point_links_checked20452 : (cuts20452.take 2).map (fun c => (2684616705-1+2*2^9*c.k,100310264817188+c.lower,100310645356464+c.upper)) = pointBounds20452 := by
 decide +kernel
def cuts20453 : List PrefixCut := [⟨64,319030949,319031129⟩,
⟨128,633441242,633441604⟩]
theorem checked20453 : checkPrefixCuts (2^48) 2684747777 9 Manual.Count131072.C020453.packed 128 cuts20453 = true := by
 decide +kernel
def pointBounds20453 : List (Nat × Nat × Nat) := [(2684813312,100311212392609,100311592932435)]
theorem point_links_checked20453 : (cuts20453.take 1).map (fun c => (2684747777-1+2*2^9*c.k,100310893361660+c.lower,100311273901306+c.upper)) = pointBounds20453 := by
 decide +kernel
def cuts20454 : List PrefixCut := [⟨18,85756454,85756505⟩,
⟨100,492724851,492725147⟩,
⟨128,634353608,634353986⟩]
theorem checked20454 : checkPrefixCuts (2^48) 2684878849 9 Manual.Count131072.C020454.packed 128 cuts20454 = true := by
 decide +kernel
def pointBounds20454 : List (Nat × Nat × Nat) := [(2684897280,100311612559356,100311993099415),(2684981248,100312019527753,100312400068057)]
theorem point_links_checked20454 : (cuts20454.take 2).map (fun c => (2684878849-1+2*2^9*c.k,100311526802902+c.lower,100311907342910+c.upper)) = pointBounds20454 := by
 decide +kernel
def cuts20455 : List PrefixCut := [⟨54,261762761,261762915⟩,
⟨128,632855123,632855490⟩]
theorem checked20455 : checkPrefixCuts (2^48) 2685009921 9 Manual.Count131072.C020455.packed 128 cuts20455 = true := by
 decide +kernel
def pointBounds20455 : List (Nat × Nat × Nat) := [(2685065216,100312422919271,100312803459811)]
theorem point_links_checked20455 : (cuts20455.take 1).map (fun c => (2685009921-1+2*2^9*c.k,100312161156510+c.lower,100312541696896+c.upper)) = pointBounds20455 := by
 decide +kernel
def cuts20456 : List PrefixCut := [⟨8,41721026,41721051⟩,
⟨90,440894260,440894521⟩,
⟨128,627163866,627164234⟩]
theorem checked20456 : checkPrefixCuts (2^48) 2685140993 9 Manual.Count131072.C020456.packed 128 cuts20456 = true := by
 decide +kernel
def pointBounds20456 : List (Nat × Nat × Nat) := [(2685149184,100312835732659,100313216273437),(2685233152,100313234905893,100313615446907)]
theorem point_links_checked20456 : (cuts20456.take 2).map (fun c => (2685140993-1+2*2^9*c.k,100312794011633+c.lower,100313174552386+c.upper)) = pointBounds20456 := by
 decide +kernel
def cuts20457 : List PrefixCut := [⟨44,217608144,217608267⟩,
⟨126,617280559,617280918⟩,
⟨128,626504426,626504790⟩]
theorem checked20457 : checkPrefixCuts (2^48) 2685272065 9 Manual.Count131072.C020457.packed 128 cuts20457 = true := by
 decide +kernel
def pointBounds20457 : List (Nat × Nat × Nat) := [(2685317120,100313638783643,100314019324887),(2685401088,100314038456058,100314418997538)]
theorem point_links_checked20457 : (cuts20457.take 2).map (fun c => (2685272065-1+2*2^9*c.k,100313421175499+c.lower,100313801716620+c.upper)) = pointBounds20457 := by
 decide +kernel
def cuts20458 : List PrefixCut := [⟨80,398401897,398402133⟩,
⟨128,634649206,634649585⟩]
theorem checked20458 : checkPrefixCuts (2^48) 2685403137 9 Manual.Count131072.C020458.packed 128 cuts20458 = true := by
 decide +kernel
def pointBounds20458 : List (Nat × Nat × Nat) := [(2685485056,100314446081822,100314826623543)]
theorem point_links_checked20458 : (cuts20458.take 1).map (fun c => (2685403137-1+2*2^9*c.k,100314047679925+c.lower,100314428221410+c.upper)) = pointBounds20458 := by
 decide +kernel
def cuts20459 : List PrefixCut := [⟨34,163295271,163295367⟩,
⟨116,572362960,572363295⟩,
⟨128,631369091,631369461⟩]
theorem checked20459 : checkPrefixCuts (2^48) 2685534209 9 Manual.Count131072.C020459.packed 128 cuts20459 = true := by
 decide +kernel
def pointBounds20459 : List (Nat × Nat × Nat) := [(2685569024,100314845624402,100315226166362),(2685652992,100315254692091,100315635234290)]
theorem point_links_checked20459 : (cuts20459.take 2).map (fun c => (2685534209-1+2*2^9*c.k,100314682329131+c.lower,100315062870995+c.upper)) = pointBounds20459 := by
 decide +kernel
def cuts20460 : List PrefixCut := [⟨70,341978705,341978911⟩,
⟨128,633539103,633539477⟩]
theorem checked20460 : checkPrefixCuts (2^48) 2685665281 9 Manual.Count131072.C020460.packed 128 cuts20460 = true := by
 decide +kernel
def pointBounds20460 : List (Nat × Nat × Nat) := [(2685736960,100315655676927,100316036219367)]
theorem point_links_checked20460 : (cuts20460.take 1).map (fun c => (2685665281-1+2*2^9*c.k,100315313698222+c.lower,100315694240456+c.upper)) = pointBounds20460 := by
 decide +kernel
def cuts20461 : List PrefixCut := [⟨24,117272086,117272158⟩,
⟨106,519489350,519489656⟩,
⟨128,626277090,626277459⟩]
theorem checked20461 : checkPrefixCuts (2^48) 2685796353 9 Manual.Count131072.C020461.packed 128 cuts20461 = true := by
 decide +kernel
def pointBounds20461 : List (Nat × Nat × Nat) := [(2685820928,100316064509411,100316445052091),(2685904896,100316466726675,100316847269589)]
theorem point_links_checked20461 : (cuts20461.take 2).map (fun c => (2685796353-1+2*2^9*c.k,100315947237325+c.lower,100316327779933+c.upper)) = pointBounds20461 := by
 decide +kernel
def cuts20462 : List PrefixCut := [⟨60,295836211,295836384⟩,
⟨128,632429414,632429787⟩]
theorem checked20462 : checkPrefixCuts (2^48) 2685927425 9 Manual.Count131072.C020462.packed 128 cuts20462 = true := by
 decide +kernel
def pointBounds20462 : List (Nat × Nat × Nat) := [(2685988864,100316869350626,100317249893776)]
theorem point_links_checked20462 : (cuts20462.take 1).map (fun c => (2685927425-1+2*2^9*c.k,100316573514415+c.lower,100316954057392+c.upper)) = pointBounds20462 := by
 decide +kernel
def cuts20463 : List PrefixCut := [⟨14,68952328,68952369⟩,
⟨96,481610926,481611210⟩,
⟨128,640781747,640782124⟩]
theorem checked20463 : checkPrefixCuts (2^48) 2686058497 9 Manual.Count131072.C020463.packed 128 cuts20463 = true := by
 decide +kernel
def pointBounds20463 : List (Nat × Nat × Nat) := [(2686072832,100317274896157,100317655439548),(2686156800,100317687554755,100318068098389)]
theorem point_links_checked20463 : (cuts20463.take 2).map (fun c => (2686058497-1+2*2^9*c.k,100317205943829+c.lower,100317586487179+c.upper)) = pointBounds20463 := by
 decide +kernel
def cuts20464 : List PrefixCut := [⟨50,247816362,247816512⟩,
⟨128,631948590,631948962⟩]
theorem checked20464 : checkPrefixCuts (2^48) 2686189569 9 Manual.Count131072.C020464.packed 128 cuts20464 = true := by
 decide +kernel
def pointBounds20464 : List (Nat × Nat × Nat) := [(2686240768,100318094541938,100318475085815)]
theorem point_links_checked20464 : (cuts20464.take 1).map (fun c => (2686189569-1+2*2^9*c.k,100317846725576+c.lower,100318227269303+c.upper)) = pointBounds20464 := by
 decide +kernel
def cuts20465 : List PrefixCut := [⟨4,18965315,18965325⟩,
⟨86,424040998,424041247⟩,
⟨128,627621858,627622227⟩]
theorem checked20465 : checkPrefixCuts (2^48) 2686320641 9 Manual.Count131072.C020465.packed 128 cuts20465 = true := by
 decide +kernel
def pointBounds20465 : List (Nat × Nat × Nat) := [(2686324736,100318497639481,100318878183590),(2686408704,100318902715164,100319283259512)]
theorem point_links_checked20465 : (cuts20465.take 2).map (fun c => (2686320641-1+2*2^9*c.k,100318478674166+c.lower,100318859218265+c.upper)) = pointBounds20465 := by
 decide +kernel
def cuts20466 : List PrefixCut := [⟨40,196243427,196243541⟩,
⟨122,604332199,604332550⟩,
⟨128,634506167,634506536⟩]
theorem checked20466 : checkPrefixCuts (2^48) 2686451713 9 Manual.Count131072.C020466.packed 128 cuts20466 = true := by
 decide +kernel
def pointBounds20466 : List (Nat × Nat × Nat) := [(2686492672,100319302539451,100319683084033),(2686576640,100319710628223,100320091173042)]
theorem point_links_checked20466 : (cuts20466.take 2).map (fun c => (2686451713-1+2*2^9*c.k,100319106296024+c.lower,100319486840492+c.upper)) = pointBounds20466 := by
 decide +kernel
def cuts20467 : List PrefixCut := [⟨76,375282868,375283085⟩,
⟨128,635103856,635104223⟩]
theorem checked20467 : checkPrefixCuts (2^48) 2686582785 9 Manual.Count131072.C020467.packed 128 cuts20467 = true := by
 decide +kernel
def pointBounds20467 : List (Nat × Nat × Nat) := [(2686660608,100320116085059,100320496630113)]
theorem point_links_checked20467 : (cuts20467.take 1).map (fun c => (2686582785-1+2*2^9*c.k,100319740802191+c.lower,100320121347028+c.upper)) = pointBounds20467 := by
 decide +kernel
def cuts20468 : List PrefixCut := [⟨30,145623205,145623289⟩,
⟨112,548540376,548540698⟩,
⟨128,628158513,628158880⟩]
theorem checked20468 : checkPrefixCuts (2^48) 2686713857 9 Manual.Count131072.C020468.packed 128 cuts20468 = true := by
 decide +kernel
def pointBounds20468 : List (Nat × Nat × Nat) := [(2686744576,100320521529252,100320902074540),(2686828544,100320924446423,100321304991949)]
theorem point_links_checked20468 : (cuts20468.take 2).map (fun c => (2686713857-1+2*2^9*c.k,100320375906047+c.lower,100320756451251+c.upper)) = pointBounds20468 := by
 decide +kernel
def cuts20469 : List PrefixCut := [⟨66,329991042,329991234⟩,
⟨128,633784953,633785328⟩]
theorem checked20469 : checkPrefixCuts (2^48) 2686844929 9 Manual.Count131072.C020469.packed 128 cuts20469 = true := by
 decide +kernel
def pointBounds20469 : List (Nat × Nat × Nat) := [(2686912512,100321334055602,100321714601365)]
theorem point_links_checked20469 : (cuts20469.take 1).map (fun c => (2686844929-1+2*2^9*c.k,100321004064560+c.lower,100321384610131+c.upper)) = pointBounds20469 := by
 decide +kernel
def cuts20470 : List PrefixCut := [⟨20,100878940,100879000⟩,
⟨102,508786420,508786721⟩,
⟨128,636582266,636582641⟩]
theorem checked20470 : checkPrefixCuts (2^48) 2686976001 9 Manual.Count131072.C020470.packed 128 cuts20470 = true := by
 decide +kernel
def pointBounds20470 : List (Nat × Nat × Nat) := [(2686996480,100321738728453,100322119274459),(2687080448,100322146635933,100322527182180)]
theorem point_links_checked20470 : (cuts20470.take 2).map (fun c => (2686976001-1+2*2^9*c.k,100321637849513+c.lower,100322018395459+c.upper)) = pointBounds20470 := by
 decide +kernel
def cuts20471 : List PrefixCut := [⟨57,287326570,287326737⟩,
⟨128,643674066,643674438⟩]
theorem checked20471 : checkPrefixCuts (2^48) 2687107073 9 Manual.Count131072.C020471.packed 128 cuts20471 = true := by
 decide +kernel
def pointBounds20471 : List (Nat × Nat × Nat) := [(2687165440,100322561758349,100322942304837)]
theorem point_links_checked20471 : (cuts20471.take 1).map (fun c => (2687107073-1+2*2^9*c.k,100322274431779+c.lower,100322654978100+c.upper)) = pointBounds20471 := by
 decide +kernel
def cuts20472 : List PrefixCut := [⟨12,61799440,61799475⟩,
⟨95,478152494,478152767⟩,
⟨128,641233619,641233992⟩]
theorem checked20472 : checkPrefixCuts (2^48) 2687238145 9 Manual.Count131072.C020472.packed 128 cuts20472 = true := by
 decide +kernel
def pointBounds20472 : List (Nat × Nat × Nat) := [(2687250432,100322979905285,100323360452013),(2687335424,100323396258339,100323776805305)]
theorem point_links_checked20472 : (cuts20472.take 2).map (fun c => (2687238145-1+2*2^9*c.k,100322918105845+c.lower,100323298652538+c.upper)) = pointBounds20472 := by
 decide +kernel
def cuts20473 : List PrefixCut := [⟨50,254306158,254306305⟩,
⟨128,634813552,634813921⟩]
theorem checked20473 : checkPrefixCuts (2^48) 2687369217 9 Manual.Count131072.C020473.packed 128 cuts20473 = true := by
 decide +kernel
def pointBounds20473 : List (Nat × Nat × Nat) := [(2687420416,100323813645622,100324194192835)]
theorem point_links_checked20473 : (cuts20473.take 1).map (fun c => (2687369217-1+2*2^9*c.k,100323559339464+c.lower,100323939886530+c.upper)) = pointBounds20473 := by
 decide +kernel
def cuts20474 : List PrefixCut := [⟨5,26078948,26078962⟩,
⟨88,439878977,439879228⟩,
⟨128,636458173,636458541⟩]
theorem checked20474 : checkPrefixCuts (2^48) 2687500289 9 Manual.Count131072.C020474.packed 128 cuts20474 = true := by
 decide +kernel
def pointBounds20474 : List (Nat × Nat × Nat) := [(2687505408,100324220231964,100324600779413),(2687590400,100324634031993,100325014579679)]
theorem point_links_checked20474 : (cuts20474.take 2).map (fun c => (2687500289-1+2*2^9*c.k,100324194153016+c.lower,100324574700451+c.upper)) = pointBounds20474 := by
 decide +kernel
def cuts20475 : List PrefixCut := [⟨43,211133380,211133499⟩,
⟨126,621032323,621032680⟩,
⟨128,630562267,630562630⟩]
theorem checked20475 : checkPrefixCuts (2^48) 2687631361 9 Manual.Count131072.C020475.packed 128 cuts20475 = true := by
 decide +kernel
def pointBounds20475 : List (Nat × Nat × Nat) := [(2687675392,100325041744569,100325422292491),(2687760384,100325451643512,100325832191672)]
theorem point_links_checked20475 : (cuts20475.take 2).map (fun c => (2687631361-1+2*2^9*c.k,100324830611189+c.lower,100325211158992+c.upper)) = pointBounds20475 := by
 decide +kernel
def cuts20476 : List PrefixCut := [⟨81,400565518,400565754⟩,
⟨128,633568536,633568909⟩]
theorem checked20476 : checkPrefixCuts (2^48) 2687762433 9 Manual.Count131072.C020476.packed 128 cuts20476 = true := by
 decide +kernel
def pointBounds20476 : List (Nat × Nat × Nat) := [(2687845376,100325861738974,100326242287376)]
theorem point_links_checked20476 : (cuts20476.take 1).map (fun c => (2687762433-1+2*2^9*c.k,100325461173456+c.lower,100325841721622+c.upper)) = pointBounds20476 := by
 decide +kernel
def cuts20477 : List PrefixCut := [⟨36,177393633,177393737⟩,
⟨119,591128243,591128588⟩,
⟨128,636155512,636155883⟩]
theorem checked20477 : checkPrefixCuts (2^48) 2687893505 9 Manual.Count131072.C020477.packed 128 cuts20477 = true := by
 decide +kernel
def pointBounds20477 : List (Nat × Nat × Nat) := [(2687930368,100326272135625,100326652684268),(2688015360,100326685870235,100327066419119)]
theorem point_links_checked20477 : (cuts20477.take 2).map (fun c => (2687893505-1+2*2^9*c.k,100326094741992+c.lower,100326475290531+c.upper)) = pointBounds20477 := by
 decide +kernel
def cuts20478 : List PrefixCut := [⟨74,367332965,367333173⟩,
⟨128,633820852,633821214⟩]
theorem checked20478 : checkPrefixCuts (2^48) 2688024577 9 Manual.Count131072.C020478.packed 128 cuts20478 = true := by
 decide +kernel
def pointBounds20478 : List (Nat × Nat × Nat) := [(2688100352,100327098230469,100327478779587)]
theorem point_links_checked20478 : (cuts20478.take 1).map (fun c => (2688024577-1+2*2^9*c.k,100326730897504+c.lower,100327111446414+c.upper)) = pointBounds20478 := by
 decide +kernel
def cuts20479 : List PrefixCut := [⟨29,139786152,139786234⟩,
⟨112,554947438,554947764⟩,
⟨128,634104044,634104417⟩]
theorem checked20479 : checkPrefixCuts (2^48) 2688155649 9 Manual.Count131072.C020479.packed 128 cuts20479 = true := by
 decide +kernel
def pointBounds20479 : List (Nat × Nat × Nat) := [(2688185344,100327504504508,100327885053862),(2688270336,100327919665794,100328300215392)]
theorem point_links_checked20479 : (cuts20479.take 2).map (fun c => (2688155649-1+2*2^9*c.k,100327364718356+c.lower,100327745267628+c.upper)) = pointBounds20479 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000014
