import './Navbar.css';
import { Link } from "react-router-dom";


export default function Navbar(props) {

  return (
    <nav className="Sidebar">
      <ul className="Main-Nav">
        <li className="Nav-Item">
          <Link to="/overview">Overview</Link>
        </li>
        <li className="Nav-Item">
          <Link to="/overview">Components</Link>
            <ul className="Hidden-Nav">
              <li className="Nav-Subitem">Manage Components</li>
            </ul>
        </li>
        <li className="Nav-Item">Groups
            <ul className="Hidden-Nav">
              <li className="Nav-Subitem">Manage Groups</li>
            </ul>
        </li>
        <li className="Nav-Item">Tags
            <ul className="Hidden-Nav">
              <li className="Nav-Subitem">Manage Groups</li>
            </ul>
        </li>
        <li className="Nav-Item">Rules</li>
        <li className="Nav-Item">Solution Viewer</li>
      </ul>
    </nav>    
  );
}