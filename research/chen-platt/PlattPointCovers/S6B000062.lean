import PlattPointSubsetKernel
import PlattPointPackets.S1B000486
import PlattPointPackets.S1B000487
import PlattPointPackets.S1B000488
import PlattPointPackets.S1B000489
import PlattPointPackets.S1B000490
import PlattGlobalGrid.S6B000062
namespace ChenEffective.PlattWindow.PointCovers.S6B000062
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S1B000486.points ++ ChenEffective.PlattWindow.PointPackets.S1B000487.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000488.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000489.points) ++ ChenEffective.PlattWindow.PointPackets.S1B000490.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S6B000062.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S6B000062.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S6B000062
