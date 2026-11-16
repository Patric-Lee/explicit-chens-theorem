import PlattPointSubsetKernel
import PlattPointPackets.S1B000347
import PlattPointPackets.S1B000348
import PlattPointPackets.S1B000349
import PlattPointPackets.S1B000350
import PlattGlobalGrid.S6B000018
namespace ChenEffective.PlattWindow.PointCovers.S6B000018
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S1B000347.points ++ ChenEffective.PlattWindow.PointPackets.S1B000348.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000349.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000350.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000018.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000018.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000018
