import PlattPointSubsetKernel
import PlattPointPackets.S1B000517
import PlattPointPackets.S1B000518
import PlattPointPackets.S1B000519
import PlattPointPackets.S1B000520
import PlattPointPackets.S1B000521
import PlattGlobalGrid.S6B000070
namespace ChenEffective.PlattWindow.PointCovers.S6B000070
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000517.points ++ ChenEffective.PlattWindow.PointPackets.S1B000518.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000519.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000520.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000521.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000070.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000070.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000070
