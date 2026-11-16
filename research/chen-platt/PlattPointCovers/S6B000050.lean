import PlattPointSubsetKernel
import PlattPointPackets.S1B000443
import PlattPointPackets.S1B000444
import PlattPointPackets.S1B000445
import PlattPointPackets.S1B000446
import PlattPointPackets.S1B000447
import PlattGlobalGrid.S6B000050
namespace ChenEffective.PlattWindow.PointCovers.S6B000050
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000443.points ++ ChenEffective.PlattWindow.PointPackets.S1B000444.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000445.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000446.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000447.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000050.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000050.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000050
